import Data.Fin
import Data.Vect

%default total

data Frame : Type where
     Strike : Frame
     Spare : (first : Fin 10) -> Frame
     Pins : (first : Nat) -> 
            (second : Nat) ->
            {auto prf : LT (first + second) 10} -> 
            Frame

bonus : Frame -> Type
bonus Strike = (Fin 11, Fin 11)
bonus (Spare _) = (Fin 11)
bonus (Pins _ _) = ()

FrameAndBonus : Type
FrameAndBonus = (frame : Frame ** bonus frame)

data GameScore : Type where 
  MkGameScore : Vect 9 Frame -> FrameAndBonus -> GameScore

score : FrameAndBonus -> Nat
score (Strike ** (b1, b2)) = 10 + finToNat b1 + finToNat b2
score ((Spare _) ** b1) = 10 + finToNat b1
score ((Pins first second) ** ()) = first + second

throws : Frame -> Type
throws Strike = Fin 11
throws _ = (Fin 11, Fin 11)

throwsHelp : (frame : Frame) -> throws frame
throwsHelp Strike = 10
throwsHelp (Spare first) = 
  (weaken first, restrict 10 (10 - finToInteger first))
throwsHelp (Pins first second) =
  (restrict 10 (toIntegerNat first), restrict 10 (toIntegerNat second))

firstThrow : Frame -> Fin 11
firstThrow Strike = throwsHelp Strike
firstThrow (Spare first) = fst $ throwsHelp (Spare first)
firstThrow (Pins first second) = fst $ throwsHelp (Pins first second)

twoThrows : (f1 : Frame ** throws f1) -> 
            (f2 : Frame ** throws f2) -> 
            (Fin 11, Fin 11)
twoThrows (Strike ** t1) (Strike ** t2) = (t1, t2)
twoThrows (Strike ** t1) (Spare _ ** (t2,_)) = (t1, t2)
twoThrows (Strike ** t1) (Pins _ _ ** (t2,_)) = (t1, t2)
twoThrows (Spare _ ** (t1,t2)) _ = (t1,t2)
twoThrows (Pins _ _ ** (t1,t2)) _ = (t1,t2)

initBonus : (current : Frame) ->
            (next : Frame) ->
            (third : Frame) ->
            bonus current
initBonus Strike next third = 
  twoThrows (next ** throwsHelp next) (third ** throwsHelp third)
initBonus (Spare _) next _ = firstThrow next
initBonus (Pins _ _) _ _ = ()

twoBonus : (frame : Frame) -> 
           throws frame ->
           bonus frame -> 
           (Fin 11, Fin 11)
twoBonus Strike t1 (t2,_) = (t1,t2)
twoBonus (Spare _) (t1,t2) _ = (t1,t2)
twoBonus (Pins _ _) (t1,t2) _ = (t1,t2)

ninthBonus : (ninth : Frame) -> 
             (tenth : Frame) -> 
             bonus tenth -> 
             bonus ninth
ninthBonus Strike tenth tenthBonus =
   twoBonus tenth (throwsHelp tenth) tenthBonus
ninthBonus (Spare _) tenth _ = firstThrow tenth
ninthBonus (Pins _ _) _ _ = ()

vectCommutative : Vect (m + n) elem -> Vect (n + m) elem
vectCommutative {m} {n} xs = rewrite sym (plusCommutative m n) in xs

triplewise : Vect (2 + n) elem -> Vect n (elem, elem, elem)
triplewise {n} xs = zip3 first second third where
  first  = take n $ vectCommutative xs
  second = let (_ :: tail) = xs in init tail
  third  = drop 2 xs

frames : GameScore -> Vect 10 FrameAndBonus
frames (MkGameScore frames (tenth ** tenthBonus)) = 
  map (\(f1,f2,f3) => (f1 ** initBonus f1 f2 f3))
      (triplewise (frames ++ [tenth])) 
  ++ rest
where
  ninth : Frame 
  ninth = last frames
  ninthB : bonus ninth
  ninthB = ninthBonus ninth tenth tenthBonus
  rest = [(ninth ** ninthB), (tenth ** tenthBonus)]

points : GameScore -> Nat
points = sum . map score . frames

sampleGame : GameScore
sampleGame = MkGameScore 
          ([Strike, Pins 2 7, Spare 2, Strike, Strike,
            Strike, Spare 9,  Strike,  Strike])
          (Strike ** (9, 8))

main : IO ()
main = putStrLn $ show $ points sampleGame