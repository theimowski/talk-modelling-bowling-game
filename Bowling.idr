import Data.Fin
import Data.Vect

%default total

data FrameScore : Type where
     Strike : FrameScore
     Spare : (first : Fin 10) -> FrameScore
     Pins : (first : Nat) -> 
            (second : Nat) ->
            {auto prf : LT (first + second) 10} -> 
            FrameScore

bonus : FrameScore -> Type
bonus Strike = (Fin 11, Fin 11)
bonus (Spare x) = (Fin 11)
bonus (Pins first second) = ()

data GameScore : Type where
     MkGameScore : Vect 9 FrameScore -> 
                   (lastFrame : FrameScore) -> 
                   (bonus lastFrame) ->
                   GameScore

vectCommutative : Vect (m + n) elem -> Vect (n + m) elem
vectCommutative {m} {n} xs = rewrite sym (plusCommutative m n) in xs

middle : Vect (2 + n) elem -> Vect n elem
middle (x :: xs) = init xs

triplewise : Vect (2 + n) elem -> Vect n (elem, elem, elem)
triplewise {n} xs = zip3 first second third where
  first  = take n $ vectCommutative xs
  second = middle xs
  third  = drop 2 xs

frameScore : (frame : FrameScore) -> (bonus : bonus frame) -> Nat
frameScore Strike (bonus1, bonus2) = 
    10 + finToNat bonus1 + finToNat bonus2
frameScore (Spare x) bonus = 
    10 + finToNat bonus
frameScore (Pins first second) () =
    first + second

firstThrow : FrameScore -> Fin 11
firstThrow Strike = 10
firstThrow (Spare x) = weaken x
firstThrow (Pins first _) = restrict 10 (toIntegerNat first)

secondThrow : FrameScore -> Maybe (Fin 11)
secondThrow Strike = Nothing
secondThrow (Spare x) = Just $ restrict 10 (10 - finToInteger x)
secondThrow (Pins _ second) = Just $ restrict 10 (toIntegerNat second)

throws : FrameScore -> Type
throws Strike = Fin 11
throws _ = (Fin 11, Fin 11)

throwsHelp : (frame : FrameScore) -> throws frame
throwsHelp Strike = 10
throwsHelp (Spare first) = 
  (weaken first, restrict 10 (10 - finToInteger first))
throwsHelp (Pins first second) =
  (restrict 10 (toIntegerNat first), restrict 10 (toIntegerNat second))

twoThrows : FrameScore -> FrameScore -> (Fin 11, Fin 11)
twoThrows f1 f2 with (firstThrow f1, secondThrow f1, firstThrow f2)
  | (first, Just second, _) = (first, second)
  | (first, Nothing, second) = (first, second)

initBonus : (current : FrameScore) ->
            (next : FrameScore) ->
            (third : FrameScore) ->
            bonus current
initBonus Strike next third = twoThrows next third
initBonus (Spare _) next _ = firstThrow next
initBonus (Pins _ _) _ _ = ()

twoBonus : (frame : FrameScore) -> 
           throws frame ->
           bonus frame -> 
           (Fin 11, Fin 11)
twoBonus Strike t1 (t2,_) = (t1,t2)
twoBonus (Spare _) (t1,t2) _ = (t1,t2)
twoBonus (Pins _ _) (t1,t2) _ = (t1,t2)

ninthBonus : (ninth : FrameScore) -> 
             (tenth : FrameScore) -> 
             bonus tenth -> 
             bonus ninth
ninthBonus Strike tenth tenthBonus =
   twoBonus tenth (throwsHelp tenth) tenthBonus
ninthBonus (Spare _) tenth _ = firstThrow tenth
ninthBonus (Pins _ _) _ _ = ()

frames : GameScore -> Vect 10 (f' ** bonus f')
frames (MkGameScore xs tenth tenthBonus) = 
  map (\(s1,s2,s3) => (s1 ** initBonus s1 s2 s3))
      (triplewise (xs ++ [tenth])) ++ rest
where
  ninth : FrameScore 
  ninth = index 8 xs
  ninthB : bonus ninth
  ninthB = ninthBonus ninth tenth tenthBonus
  rest = [(ninth ** ninthB), (tenth ** tenthBonus)]

frameScores : GameScore -> Vect 10 Nat
frameScores score = 
  map (\(x ** y) => frameScore x y) $ frames score

countScore : GameScore -> Nat
countScore score = sum (frameScores score)

score : GameScore
score = MkGameScore 
          ([Strike, Pins 2 7, Spare 2, Strike, Strike,
            Strike, Spare 9,  Strike,  Strike])
          Strike
          (9, 8)

main : IO ()
main = putStrLn $ show $ countScore score