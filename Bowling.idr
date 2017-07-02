import Data.Fin
import Data.Vect

%default total

data FrameScore : Type where
     Strike : FrameScore
     Spare : Fin 10 -> FrameScore
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

score : GameScore
score = MkGameScore 
          ([Strike, Pins 2 7, Spare 2, Strike, Strike,
            Strike, Spare 9,  Strike,  Strike])
          Strike
          (9, 8)

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

nextThrows : FrameScore -> FrameScore -> (Fin 11, Fin 11)
nextThrows Strike Strike = (10, 10)
nextThrows Strike (Spare x) = (10, weaken x)
nextThrows Strike (Pins first _) = (10, ?nextThrows_rhs_6)
nextThrows (Spare x) _ = (weaken x, ?nextThrows_rhs_2)
nextThrows (Pins first second) _ = ?nextThrows_rhs_3

initBonus : (current : FrameScore) ->
            (next : FrameScore) ->
            (third : FrameScore) ->
            bonus current

ninthBonus : (ninth : FrameScore) -> 
             (tenth : FrameScore) -> 
             (tenthBonus : bonus tenth) -> 
             bonus ninth
ninthBonus Strike Strike (b1, _) = (10, b1)
ninthBonus Strike (Spare x) _ = (weaken x, ?ninthBonus_rhs_5)
ninthBonus Strike (Pins first second) _ = ?ninthBonus_rhs_6
ninthBonus (Spare _) Strike _ = 10
ninthBonus (Spare _) (Spare x) _ = weaken x
ninthBonus (Spare _) (Pins first _) _ = ?ninthBonus_rhs_3
ninthBonus (Pins _ _) _ _ = ()

frames : GameScore -> Vect 10 (f' ** bonus f')
frames (MkGameScore xs tenth tenthBonus) = 
  map framesHelp (triplewise (xs ++ [tenth])) ++ rest
where
  framesHelp (Strike,s2,s3) with (nextThrows s2 s3)
    | (t1, t2) = (Strike ** (t1, t2))
  framesHelp (Spare x,s2,s3) with (nextThrows s2 s3)
    | (t, _) = (Spare x ** t)
  framesHelp (Pins x y,_,_) = (Pins x y ** ())
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

main : IO ()
main = putStrLn $ show $ frameScore (Strike) (5, 10)