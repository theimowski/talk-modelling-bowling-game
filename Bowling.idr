import Data.Fin
import Data.Vect

%default total

data FrameScore : Type where
     Strike : FrameScore
     Spare : Fin 10 -> FrameScore
     Pins : (first : Nat) -> (second : Nat) ->
            {auto prf : LT (first + second) 10} -> FrameScore

frameBonus : FrameScore -> Type
frameBonus Strike = (Fin 11, Fin 11)
frameBonus (Spare x) = (Fin 11)
frameBonus (Pins first second) = ()

data GameScore : Type where
     MkGameScore : Vect 9 FrameScore -> 
                   (lastFrame : FrameScore) -> 
                   (frameBonus lastFrame) ->
                   GameScore

score : GameScore
score = MkGameScore 
          ([Strike, Pins 2 7, Spare 2, Strike, Strike,
            Strike, Spare 9,  Strike,  Strike])
          Strike
          (9, 8)

flatBonus : (lastFrame : FrameScore) -> 
            (bonus : frameBonus lastFrame) 
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

vectCommutative : Vect (m + n) elem -> Vect (n + m) elem
vectCommutative {m} {n} xs = rewrite sym (plusCommutative m n) in xs

middle : Vect (2 + n) elem -> Vect n elem
middle (x :: xs) = init xs

triplewise : Vect (n + 2) elem -> Vect n (elem, elem, elem)
triplewise {n} xs = zip3 first second third where
  first  = take n xs
  second = middle $ vectCommutative xs
  third  = drop 2 $ vectCommutative xs

frameScore : (lastFrame : FrameScore) ->
                 (frameBonus : frameBonus lastFrame) -> Nat
frameScore Strike (bonus1, bonus2) = 
    10 + finToNat bonus1 + finToNat bonus2
frameScore (Spare x) bonus = 
    10 + finToNat bonus
frameScore (Pins first second) () =
    first + second

frames : Vect 9 FrameScore -> 
         (f : FrameScore) -> 
         frameBonus f ->
         Vect 9 (f' ** frameBonus f')
frames xs f x = map framesHelp xs where
  framesHelp score = (score ** ?wuuu)

frameScores : GameScore -> Vect 10 Nat
frameScores (MkGameScore xs lastFrame frameBonus) = 
  map (\(x ** y) => frameScore x y) $ 
        (frames xs lastFrame frameBonus) ++ 
        [(lastFrame ** frameBonus)]

countScore : GameScore -> Nat
countScore score = sum (frameScores score)

main : IO ()
main = putStrLn $ show $ frameScore (Strike) (5, 10)