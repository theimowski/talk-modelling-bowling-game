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
                   (last : FrameScore) -> 
                   (lastFrameBonus last) ->
                   GameScore

score : GameScore
score = MkGameScore 
          ([Strike, Pins 2 7, Spare 2, Strike, Strike,
            Strike, Spare 9,  Strike,  Strike])
          Strike
          (9, 8)

main : IO ()
main = pure ()