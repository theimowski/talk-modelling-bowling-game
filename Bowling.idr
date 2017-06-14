import Data.Fin
import Data.Vect

%default total

data FrameScore : Type where
     Strike : FrameScore
     Spare : Fin 10 -> FrameScore
     Pins : (first : Nat) -> (second : Nat) ->
            {auto prf : LT (first + second) 10} -> FrameScore

lastFrameBonus : FrameScore -> Type
lastFrameBonus Strike = (Fin 11, Fin 11)
lastFrameBonus (Spare x) = (Fin 11)
lastFrameBonus (Pins first second) = ()

data GameScore : Type where
     MkGameScore : Vect 9 FrameScore -> 
                   (lastFrame : FrameScore) -> 
                   (lastFrameBonus lastFrame) ->
                   GameScore

score : GameScore
score = MkGameScore 
          ([Strike, Pins 2 7, Spare 2, Strike, Strike,
            Strike, Spare 9,  Strike,  Strike])
          Strike
          (9, 8)

flatBonus : (lastFrame : FrameScore) -> 
            (bonus : lastFrameBonus lastFrame) 
            -> List Integer
flatBonus Strike (a, b) = map finToInteger [a,b]
flatBonus (Spare x) a = [finToInteger a]
flatBonus (Pins first second) _ = []

flat : GameScore -> List Integer
flat (MkGameScore xs lastFrame bonus) = 
    (toList xs >>= flatFrame) 
    ++ (flatFrame lastFrame) 
    ++ (flatBonus lastFrame bonus) 
    where
        flatFrame : FrameScore -> List Integer
        flatFrame Strike = [10]
        flatFrame (Spare x) with (finToInteger x)
          | y = [y, 10 - y]
        flatFrame (Pins first second) = 
          map toIntegerNat [first, second]

countHelp : List Integer -> Integer
countHelp (10 :: y :: z :: xs) = 
           10 + y + z + countHelp (y :: z :: xs)
countHelp  (x :: y :: z :: xs) = frame + countHelp (z :: xs)
  where 
    frame : Integer
    frame = if x + y == 10 then 10 + z else x + y
countHelp (x :: xs) = x + countHelp xs
countHelp [] = 0

incorrectCountScore : GameScore -> Integer
incorrectCountScore score = countHelp $ flat score

lastFrameScore : (lastFrame : FrameScore) ->
                 (lastFrameBonus : lastFrameBonus lastFrame) -> Nat
lastFrameScore Strike (bonus1, bonus2) = 
    10 + finToNat bonus1 + finToNat bonus2
lastFrameScore (Spare x) bonus = 
    10 + finToNat bonus
lastFrameScore (Pins first second) () =
    first + second

frameX : Vect 9 FrameScore -> 
         (f : FrameScore) -> 
         lastFrameBonus f ->
         Vect 9 (fs ** lastFrameBonus fs)

frameScores : GameScore -> Vect 10 Nat
frameScores (MkGameScore xs lastFrame lastFrameBonus) = 
  (lastFrameScore lastFrame lastFrameBonus) 
  :: ?frameScores_rhs_1

countScore : GameScore -> Nat
countScore score = sum (frameScores score)

main : IO ()
main = putStrLn $ show $ incorrectCountScore score