module tasks05part2 where

open import Data.Nat
open import Data.List hiding (map)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Function.Equality
-- open import Data.Maybe hiding (Any; All)
open import tasks05

open import Data.Char
open import Data.String hiding (_++_)


-- 6. Реализуйте sscanf.

maybeToBool : {A : Set} -> Maybe A -> Bool
maybeToBool Nothing = false
maybeToBool _ = true

charToInt : Char -> Maybe ℕ
charToInt '0' = Just 0
charToInt '1' = Just 1
charToInt '2' = Just 2
charToInt '3' = Just 3
charToInt '4' = Just 4
charToInt '5' = Just 5
charToInt '6' = Just 6
charToInt '7' = Just 7
charToInt '8' = Just 8
charToInt '9' = Just 9
charToInt _ = Nothing

charToBool : Char -> Maybe Bool
charToBool '0' = Just false
charToBool '1' = Just true
charToBool _ = Nothing

splitOnSpace : List Char -> List Char -> List Char × List Char
splitOnSpace acc (' ' ∷ xs) = (acc , xs)
splitOnSpace acc (x ∷ xs) = splitOnSpace (acc ++ x ∷ []) xs
splitOnSpace acc [] = (acc , [])

split : List Char -> List Char × List Char
split xs = splitOnSpace [] xs


mapp : {A B : Set} -> Maybe (A -> B) → Maybe A → Maybe B
mapp mf mx = mf m>>= \f ->
  mx m>>= \x ->
  mret (f x)

fst : {A B : Set} → A × B → A
fst (a , b) = a

snd : {A B : Set} → A × B → B
snd (a , b) = b

exp : ℕ -> ℕ -> ℕ
exp x 0 = 1
exp x (suc n) = x * exp x n

parseInt : List Char -> Maybe ℕ
parseInt [] = Just 0
parseInt (x ∷ xs) = mapp (mfmap (λ x -> λ y -> x * (exp 10 (length xs)) + y) (charToInt x)) (parseInt xs)

--------------------------------------------------------------------------

data FmtData : Set where
  num : FmtData
  bool : FmtData

FmtRes : (Maybe (List FmtData)) -> Set
FmtRes (Just []) = ⊤
FmtRes (Just (num ∷ xs)) = (ℕ × FmtRes (Just xs))
FmtRes (Just (bool ∷ xs)) = (Bool × FmtRes (Just xs))
FmtRes Nothing = ⊥

string-toFmtData : List Char → Maybe (List FmtData)
string-toFmtData [] = Just []
string-toFmtData ('%' ∷ 'd' ∷ xs) = mfmap (_∷_ num) (string-toFmtData xs)
string-toFmtData ('%' ∷ 'b' ∷ xs) = mfmap (_∷_ bool) (string-toFmtData xs)
string-toFmtData (' ' ∷ xs) = string-toFmtData xs
string-toFmtData _ = Nothing


parse : List Char -> (fmt : Maybe (List FmtData)) -> Maybe (FmtRes fmt)
parse xs Nothing = Nothing
parse xs (Just []) = Just tt
parse [] (Just ts) = Nothing
parse xs (Just (num ∷ ts)) = mapp (mfmap (λ x -> λ y -> (x , y)) (parseInt (fst (split xs))))
                                  (parse (snd (split xs)) (Just ts))

parse (x ∷ xs) (Just (bool ∷ ts)) = mapp (mfmap (λ x -> λ y -> (x , y)) (charToBool x)) (parse xs (Just ts))

sscanf : List Char -> (fmt : List Char) ->  Maybe (FmtRes (string-toFmtData fmt))
sscanf xs [] = Just tt
sscanf xs cs = parse xs (string-toFmtData cs)



--------------------------------------------
fmt : List Char
fmt = primStringToList "%d  %b"

test0 : Maybe (ℕ × Bool × ⊤)
test0 = sscanf (primStringToList "12 1") fmt

test1 : T (maybeToBool test0)
test1 = tt

test2Helper : Maybe (FmtRes (string-toFmtData fmt)) -> FmtRes (string-toFmtData fmt)
test2Helper Nothing = 0 , (false , tt)
test2Helper (Just x) = x

test2 : (test2Helper test0) ≡ (12 , (true , tt))
test2 = refl

test-1 : Maybe (ℕ × Bool × ⊤)
test-1 = sscanf (primStringToList "12  1") fmt

test-2 : T (maybeToBool test-1) -> Bool
test-2 ()





---
