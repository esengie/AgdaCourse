module tasks06 where

open import Data.Nat hiding (_<_)
open import Data.List hiding (filter)
open import Data.Bool
open import Data.Empty
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product

-- 1. Реализуйте любой алгоритм сортировки, используя with для паттерн матчинга на результате сравнения элементов списка.



-- 2. Определите filter через if, а не через with.
--    Докажите для этой версии filter следующую лемму:

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if (p x) then x ∷ filter p xs else filter p xs

lem : {A : Set} (p : A → Bool) (xs : List A) → length (filter p xs) ≤ length xs
lem p [] = z≤n
lem p (x ∷ xs) with p x
lem p (x ∷ xs) | false = ≤-step (lem p xs)
lem p (x ∷ xs) | true = s≤s (lem p xs)

-- 3. Докажите, что если равенство элементов A разрешимо, то и равенство элементов List A тоже разрешимо.

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

tail : {A : Set} → List A -> List A
tail [] = []
tail (x ∷ xs) = xs

foo : {A : Set} → (x y : A) (xs ys : List A) -> x ∷ xs ≡ y ∷ ys -> x ≡ y
foo x .x xs .xs refl = refl

List-Dec : {A : Set} → DecEq A → DecEq (List A)
List-Dec p [] [] = yes refl
List-Dec p [] (x ∷ ys) = no (λ ())
List-Dec p (x ∷ xs) [] = no (λ ())
List-Dec p (x ∷ xs) (y ∷ ys) with p x y | List-Dec p xs ys
List-Dec p (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
List-Dec p (x ∷ xs) (y ∷ ys) | _ | no ¬p = no (λ x₁ → ¬p (cong tail x₁))
List-Dec p (x ∷ xs) (y ∷ ys) | no ¬p | _ = no (λ xr -> ¬p (foo x y xs ys xr))

-- 4. Докажите, что предикат isEven разрешим.

DecPred : {A : Set} → (A → Set) → Set
DecPred {A} P = (a : A) → Dec (P a)

isEven : ℕ → Set
isEven n = Σ ℕ (λ k → n ≡ k * 2)

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even 0
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

lem12 : (x y : ℕ) -> suc (x * 2) ≡ y * 2 -> ⊥
lem12 x zero ()
lem12 0 (suc y) ()
lem12 (suc x) (suc y) p = lem12 x y (cong (λ x -> pred (pred x)) p)

isEven-Dec : DecPred isEven
isEven-Dec x with parity x
isEven-Dec .(k * 2) | even k = yes (k , refl)
isEven-Dec .(suc (k * 2)) | odd k = no (λ { (x , f) → lem12 k x f } )

-- 5. Докажите, что если равенство элементов A разрешимо, то любой список элементов A либо пуст, либо состоит из повторений одного элемента, либо в A существует два различных элемента.

repeat : {A : Set} → ℕ → A → List A
repeat zero a = []
repeat (suc n) a = a ∷ repeat n a

data Result (A : Set) (xs : List A) : Set where
  empty : xs ≡ [] → Result A xs
  repeated : (n : ℕ) (a : A) → xs ≡ repeat n a → Result A xs
  A-is-not-trivial : (a a' : A) → ¬ (a ≡ a') → Result A xs

data Maybe (A : Set) : Set where
  Just : A -> Maybe A
  Nothing : Maybe A

record Differ (A : Set) : Set where
  constructor differ
  field
    f1 : A
    f2 : A
    p : ¬ f1 ≡ f2

findDiffering :  {A : Set} -> DecEq A → (xs : List A) → Maybe (Differ A)
findDiffering p [] = Nothing
findDiffering p (x ∷ []) = Nothing
findDiffering p (x ∷ x₁ ∷ xs) with p x x₁
findDiffering p (x ∷ x₁ ∷ xs) | yes p₁ = findDiffering p xs
findDiffering p (x ∷ x₁ ∷ xs) | no ¬p = Just (differ x x₁ ¬p)

open Σ

lemma : {A : Set} (xs : List A) → DecEq A → Maybe (Result A xs)
lemma [] p = Just (empty refl)
lemma (x ∷ []) p = Just (repeated 1 x refl)
lemma (x ∷ x₁ ∷ xs) p with List-Dec p (x ∷ x₁ ∷ xs) (repeat (length xs + 2) x)
lemma (x ∷ x₁ ∷ xs) p  | yes p₁ = Just (repeated (length xs + 2) x p₁)
lemma (x ∷ x₁ ∷ xs) p  | no ¬p with findDiffering p xs
lemma (x₁ ∷ x₂ ∷ xs) p | no ¬p | Just (differ x y pr) = Just (A-is-not-trivial x y pr)
lemma (x ∷ x₁ ∷ xs) p  | no ¬p | Nothing = Nothing


-- 6. Определите view, представляющий число в виде частного и остатка от деления его на произвольное (неотрицательное) число m.
--    Реализуйте функцию деления.

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc x < suc y = x < y

data ModView (m : ℕ) : ℕ → Set where
  quot-rem : ∀ q r → T (r < m) → ModView m (r + q * m)

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

mod-view : (m n : ℕ) → T (isPos m) → ModView m n
mod-view = {! !}

div : ℕ → (m : ℕ) → T (isPos m) → ℕ
div n m p = {! !}
