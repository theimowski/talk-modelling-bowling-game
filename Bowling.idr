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

flat : GameScore -> List Nat
flat (MkGameScore xs lastFrame bonus) = toList xs >>= flatFrame
    where
        flatFrame : FrameScore -> List Nat
        flatFrame Strike = [10]
        flatFrame (Spare x) = [finToNat x, ?second] -- second??
        flatFrame (Pins first second) = [first, second]

countHelp : List Nat -> Nat
countHelp (x :: xs) = ?countHelp_rhs_2
countHelp [] = ?countHelp_rhs_1

countScore : GameScore -> Nat
countScore score = countHelp (flat score)

main : IO ()
main = pure ()