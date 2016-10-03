module lect05 where

open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Relation.Binary.PropositionalEquality
-- open import Data.Product
open import Data.Sum
open import Data.Char
open import Data.List
open import Data.String hiding (_++_)

-- (x : A) → B

-- ⊎

{-
data Pair : Set where
  pair : (x : ℕ) → ... → Set
-}

-- Π (x : A) B == (x : A) → B

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    a : A
    b : B a

-- Σ (x : A) B == Σ A (λ x → B)

_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' suc _ = false
suc _ ==' 0 = false
suc x ==' suc y = x ==' y

foo : Σ ℕ (λ x → T (x ==' 3))
foo = 3 , tt

bar : Σ ℕ (λ x → ℕ)
bar = 7 , 15

-- Σ (x : A) B == { x : A | B }

-- 1. Dependent records.

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

record Posℕ : Set where
  constructor posℕ
  field
    num : ℕ
    even : T (isPos num)

-- open Posℕ

-- div : ℕ → Posℕ → ℕ
-- div n k = num k

-- 2. monoid

record Monoid : Set₁ where
  field
    A : Set

    id : A
    _#_ : A → A → A

    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

xor-left : (x : Bool) → x xor false ≡ x
xor-left false = refl
xor-left true = refl

xor-assoc : (x y z : Bool) → (x xor y) xor z ≡ x xor (y xor z)
xor-assoc false y z = refl
xor-assoc true false z = refl
xor-assoc true true false = refl
xor-assoc true true true = refl

Bool-Monoid : Monoid
Bool-Monoid = record
                { A = Bool
                ; id = false
                ; _#_ = _xor_
                ; assoc = xor-assoc
                ; id-left = λ x → refl
                ; id-right = xor-left
                }

-- 3. functor

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B

    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) →
      fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

-- 4. sprintf

data FmtData : Set where
  num : FmtData
  char : Char → FmtData

Fmt : List FmtData → Set
Fmt [] = List Char
Fmt (num ∷ xs) = ℕ → Fmt xs
Fmt (char _ ∷ xs) = Fmt xs

ℕ-toString : ℕ → List Char
ℕ-toString _ = []

sprintf' : (acc : List Char) (xs : List FmtData) → Fmt xs
sprintf' acc [] = acc
sprintf' acc (num ∷ xs) = λ x → sprintf' (acc ++ ℕ-toString x) xs
sprintf' acc (char x ∷ xs) = sprintf' (acc ++ x ∷ []) xs

string-toFmtData : List Char → List FmtData
string-toFmtData [] = []
string-toFmtData ('%' ∷ 'd' ∷ xs) = num ∷ string-toFmtData xs
string-toFmtData (x ∷ xs) = char x ∷ string-toFmtData xs

sprintf : (xs : List Char) → Fmt (string-toFmtData xs)
sprintf xs = sprintf' [] (string-toFmtData xs)

string : List Char
string = sprintf (primStringToList "abc%def%dgh") 37 56
-- hg56fe37cba
