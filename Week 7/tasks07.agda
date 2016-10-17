module tasks07 where

open import Data.Nat hiding (_≤_)
open import Data.List hiding (filter)
open import Data.Unit hiding (_≤_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product

-- 1. Определите тип бесконечных бинарных деревьев, реализуйте для них функции map и reflect, которая отражает дерево горизонтально.

record Tree (A : Set) : Set where
  coinductive
  field
    root : A
    branch : Tree A × Tree A

open Tree

mapT : {A B : Set} -> (A -> B) -> Tree A -> Tree B
root (mapT f xs) = f (root xs)
branch (mapT f xs) = (mapT f (proj₁ (branch xs)), mapT f (proj₂ (branch xs)))

reflect : {A : Set} -> Tree A -> Tree A
root (reflect xs) = root xs
branch (reflect xs) = (reflect (proj₂ (branch xs)), reflect (proj₁ (branch xs)))

-- 2. Докажите эквивалентность <= и ≤.

_<=_ : ℕ → ℕ → Bool
0 <= _ = true
suc _ <= 0 = false
suc n <= suc k = n <= k

data _≤_ : ℕ → ℕ → Set where
  z≤n : (n : ℕ) → 0 ≤ n
  s≤s : (n k : ℕ) → n ≤ k → suc n ≤ suc k

<=-≤ : (n k : ℕ) → T (n <= k) → n ≤ k
<=-≤ zero zero p = z≤n 0
<=-≤ zero (suc k) p = z≤n (suc k)
<=-≤ (suc n) zero ()
<=-≤ (suc n) (suc k) p = s≤s n k (<=-≤ n k p)

≤-<= : (n k : ℕ) → n ≤ k → T (n <= k)
≤-<= zero zero p = tt
≤-<= zero (suc k) p = tt
≤-<= (suc n) zero ()
≤-<= (suc n) (suc k) (s≤s .n .k p) = ≤-<= n k p

-- 3. Докажите эквивалентность isSorted и isSorted'.

module Sorted₁ (A : Set) (_≤_ : A → A → Set) where
  leqHead : A → List A → Set
  leqHead _ [] = ⊤
  leqHead x (y ∷ _) = x ≤ y

  isSorted : List A → Set
  isSorted [] = ⊤
  isSorted (x ∷ xs) = leqHead x xs × isSorted xs

  data isSorted' : List A → Set where
    nil : isSorted' []
    cons : (x : A) (xs : List A) → leqHead x xs → isSorted' xs → isSorted' (x ∷ xs)

  isSorted-isSorted' : (xs : List A) → isSorted xs → isSorted' xs
  isSorted-isSorted' [] ps = nil
  isSorted-isSorted' (x ∷ xs) (p1 , p2) = cons x xs p1 (isSorted-isSorted' xs p2)

  isSorted'-isSorted : (xs : List A) → isSorted' xs → isSorted xs
  isSorted'-isSorted [] ps = tt
  isSorted'-isSorted (x ∷ xs) (cons .x .xs x₁ ps) = (x₁ , isSorted'-isSorted xs ps )

-- 4. Определите предикат принадлежности элемента списку.

data _∈_ {A : Set} (a : A) : List A → Set where
  here : (xs : List A) -> a ∈ (a ∷ xs)
  there : (x : A) (xs : List A) -> a ∈ xs -> a ∈ (x ∷ xs)

-- 5. Определите предикат xs ⊆ ys, означающий "список xs является подсписком ys".

data _⊆_ {A : Set} : List A -> List A → Set where
    nil : [] ⊆ []
    larger : {y : A} {xs ys : List A} -> xs ⊆ ys -> xs ⊆ (y ∷ ys)
    cons  : {x : A} {xs ys : List A} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)

-- 6. Докажите, что filter xs ⊆ xs для любого списка xs.

filter' : {A : Set} -> (A → Bool) → List A → List A
filter' p [] = []
filter' p (x ∷ xs) = if p x then x ∷ filter' p xs else filter' p xs

filterLess : {A : Set} -> (p : A -> Bool) -> (xs : List A) -> filter' p xs ⊆ xs
filterLess p [] = nil
filterLess p (x ∷ xs) with p x
filterLess p (x ∷ xs) | false = larger (filterLess p xs)
filterLess p (x ∷ xs) | true = cons (filterLess p xs)

-- 7*. Докажите следующее утверждение.

data div-dom (n k : ℕ) : Set where
  lt : n < k → div-dom n k
  geq : ¬ (n < k) → div-dom (n ∸ k) k → div-dom n k

pos-div-dom : (n k : ℕ) → ¬ (k ≡ 0) → div-dom n k
pos-div-dom = {!  !}

-- 8*. Докажите следующий принцип индукции.

ℕ-<-ind : (P : ℕ → Set) → ((n : ℕ) → ((k : ℕ) → k < n → P k) → P n) → (n : ℕ) → P n
ℕ-<-ind P h n = {!  !}

-- 9**. Докажите, что алгоритм сортировки, определенный ниже, корректен.
--      Возможно, вам понадобится добавить некоторые предположения о _≤_.

module Sorted₂ (A : Set) (_≤_ : A → A → Set) where
  leqHead : A → List A → Set
  leqHead _ [] = ⊤
  leqHead y (x ∷ _) = y ≤ x

  data isSorted : List A → Set where
    nil : isSorted []
    cons : {x : A} {xs : List A} → leqHead x xs → isSorted xs → isSorted (x ∷ xs)

module Perm (A : Set) where
  data isPerm : List A → List A → Set where
    nil : isPerm [] []
    cons : (x : A) (xs ys ys₁ ys₂ : List A) → isPerm xs (ys₁ ++ ys₂) → ys ≡ ys₁ ++ x ∷ ys₂ → isPerm (x ∷ xs) ys

  -- Вам, возможно, понадобятся эти леммы.
  isPerm-++-left : {xs ys : List A} → isPerm xs ys → (zs : List A) → isPerm (xs ++ zs) (ys ++ zs)
  isPerm-++-left p zs = {!  !}

  isPerm-++-right : {xs ys : List A} (zs : List A) → isPerm xs ys → isPerm (zs ++ xs) (zs ++ ys)
  isPerm-++-right zs p = {!  !}

  isPerm-trans : {xs ys zs : List A} → isPerm xs ys → isPerm ys zs → isPerm xs zs
  isPerm-trans p q = {!  !}

  isPerm-++ : {xs₁ xs₂ ys₁ ys₂ : List A} → isPerm xs₁ ys₁ → isPerm xs₂ ys₂ → isPerm (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  isPerm-++ {xs₁} {xs₂} {ys₁} {ys₂} p q = isPerm-trans (isPerm-++-left p xs₂) (isPerm-++-right ys₁ q)

module Sort (A : Set) (_≤_ : A → A → Bool) where
  open Sorted₂ A (λ x y → T (x ≤ y))
  open Perm A

  filter : (A → Bool) → List A → List A
  filter p [] = []
  filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

  sort : List A → ℕ → List A
  sort _ 0 = []
  sort [] _ = []
  sort (x ∷ xs) (suc n) = sort (filter (λ y → not (x ≤ y)) xs) n ++ x ∷ sort (filter (λ y → x ≤ y) xs) n

  sort-isPerm : (xs : List A) → isPerm xs (sort xs (length xs))
  sort-isPerm = {!  !}

  sort-isSorted : (xs : List A) → isSorted (sort xs (length xs))
  sort-isSorted = {!  !}

-- 10. Определите тип бинарных сортированных деревьев.
--    То есть таких деревьев, в которых для любого узла верно, что все элементы в левом поддереве меньше либо равны, чем значение в узле, которое меньше либо равно, чем все элементы в правом поддереве.
module BinTree' (A : Set) (_≤_ : A → A → Set) where
  mutual
    data BinTree : Set where
      leaf : A -> BinTree
      node  : (x : A) (left right : BinTree) -> leqHead x left -> geqHead x right -> BinTree

    leqHead : A → BinTree → Set
    leqHead x (leaf y) = x ≤ y
    leqHead x (node y _ _ _ _) = x ≤ y

    geqHead : A → BinTree → Set
    geqHead x (leaf y) = y ≤ x
    geqHead x (node y _ _ _ _) = y ≤ x
