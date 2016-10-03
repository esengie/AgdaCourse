module task2 where

open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.List
open import Function

-- 2

record Point {l} (A B : Set l) : Set l where
  constructor pt
  field
    x : A
    y : B

_==_ : (n m : ℕ) -> Bool
_==_ 0 0 = true
_==_ 0 _ = false
_==_ _ 0 = false
_==_ (suc n) (suc m) = n == m

t_t_∣_r==_ : forall {l} {A B : Set l} -> (eqA : A -> A -> Bool) -> (eqB : B -> B -> Bool) -> (x y : Point A B) -> Bool
t eqA t eqB ∣ a r== b  = (eqA (Point.x a) (Point.x b)) ∧ (eqB (Point.y a) (Point.y b))

-- Так нормально писать тесты? Ответь пожалуйста в имейле
test1 : T (t (_==_) t (_==_) ∣ pt 1 2 r== pt 1 2)
test1 = tt

-- 3.

less' : (n m : ℕ) -> Bool
less' 0 0 = false
less' 0 _ = true
less' _ 0 = false
less' (suc n) (suc m) = less' n m

lookup : {A : Set} (n : ℕ) -> (xs : List A) -> T (less' n (length xs)) -> A
lookup 0 [] ()
lookup 0 (x ∷ xs) p = x
lookup (suc n) [] ()
lookup (suc n) (x ∷ xs) p = lookup n xs p

-- 4.
_=='_ : (n m : ℕ) -> Bool
_=='_ 0 0 = true
_=='_ 0 _ = false
_=='_ _ 0 = false
_=='_ (suc n) (suc m) = n ==' m

reflN : (n : ℕ) -> T (n ==' n)
reflN zero = tt
reflN (suc n) = reflN n

assoc-proof : (x y z : ℕ) -> T (((x + y) + z) ==' (x + (y + z)))
assoc-proof zero b c = reflN (b + c)
assoc-proof (suc a) b c = assoc-proof a b c

-- 5.

module Sort {l} {A : Set l} (_<_ : A -> A -> Bool) where
  insert : A → List A → List A
  insert x [] = [ x ]
  insert x (y ∷ ys) =
    if x < y then x ∷ y ∷ ys
            else  y ∷ insert x ys

  sort : List A -> List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

_<<_ : ℕ -> ℕ -> Bool
zero << zero = false
zero << suc y = true
suc x << zero = false
suc x << suc y = x << y

open Sort _<<_

_===_ : List ℕ -> List ℕ -> Bool
[] === [] = true
[] === _ = false
_   === [] = false
(x ∷ xs) === (y ∷ ys) = (x ==' y) ∧ (xs === ys)


list : List ℕ
list = sort (1 ∷ 123 ∷ 2 ∷ 1123 ∷ 2 ∷ 231 ∷ 1 ∷ 1 ∷ [])

sorted : List ℕ
sorted = 1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 123 ∷ 231 ∷ 1123 ∷ []

test2 : T ((sort list) === sorted)
test2 = tt


--
