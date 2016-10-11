module tasks06 where

open import Data.Nat hiding (_<_)
open import Data.List hiding (filter)
open import Data.Bool
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product

-- 1. Реализуйте любой алгоритм сортировки, используя with для паттерн матчинга на результате сравнения элементов списка.

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < suc _ = true
suc x < suc y = x < y

insert : ℕ → List ℕ → List ℕ
insert x [] = x ∷ []
insert x (y ∷ ys) with x < y
... | true = x ∷ y ∷ ys
... | false =  y ∷ insert x ys

sort : List ℕ -> List ℕ
sort [] = []
sort (x ∷ xs) = insert x (sort xs)


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

head : {A : Set} -> A -> List A -> A
head x [] = x
head _ (x ∷ xs) = x

findDiffering :  {A : Set} -> DecEq A → (x : A) -> (xs : List A) -> ¬ xs ≡ repeat {A} (length xs) (head x xs) → Differ A
findDiffering p x [] p2 with p2 refl
... | ()
findDiffering p x (x₁ ∷ []) p2 with p2 refl
... | ()
findDiffering p x (x₁ ∷ x₂ ∷ xs) p2 with p x₁ x₂
findDiffering p x (x₁ ∷ x₂ ∷ xs) p2 | yes p₁ = findDiffering p x (x₂ ∷ xs)
  (λ pr -> p2 (cong (λ ys -> x₁ ∷ ys)
                    (subst (λ x -> x₂ ∷ xs ≡ x ∷ repeat (foldr (λ _ → suc) 0 xs) x)
                           (sym p₁)
                           pr)
               )
  )
findDiffering p x (x₁ ∷ x₂ ∷ xs) p2 | no ¬p = differ x₁ x₂ ¬p

open Σ

lemma : {A : Set} (xs : List A) → DecEq A → Result A xs
lemma [] p = empty refl
lemma (x ∷ []) p = repeated 1 x refl
lemma (x ∷ x₁ ∷ xs) p with List-Dec p (x ∷ x₁ ∷ xs) (repeat (length (x ∷ x₁ ∷ xs)) x)
lemma (x ∷ x₁ ∷ xs) p  | yes p₁ = repeated (length (x ∷ x₁ ∷ xs)) x p₁
lemma (x ∷ x₁ ∷ xs) p  | no ¬p with findDiffering p x (x ∷ x₁ ∷ xs) ¬p
lemma (x₁ ∷ x₂ ∷ xs) p | no ¬p | differ x y pr = A-is-not-trivial x y pr


-- 6. Определите view, представляющий число в виде частного и остатка от деления его на произвольное (неотрицательное) число m.
--    Реализуйте функцию деления.

data LessThan : ℕ -> ℕ -> Set where
  less : ∀ n m -> T (n < m) -> LessThan n m
  eq : ∀ n m -> n ≡ m -> LessThan n m
  more : ∀ n m -> T (m < n) -> LessThan n m

lessity : (n m : ℕ) -> LessThan n m
lessity 0 0 = eq 0 0 refl
lessity (suc n) 0 = more (suc n) 0 tt
lessity 0 (suc m) = less 0 (suc m) tt
lessity (suc n) (suc m) with lessity n m
lessity (suc n) (suc m) | less .n .m p = less (suc n) (suc m) p
lessity (suc n) (suc m) | eq .n .m p = eq (suc n) (suc m) (cong suc p)
lessity (suc n) (suc m) | more .n .m p = more (suc n) (suc m) p

data ModView (m : ℕ) : ℕ → Set where
  quot-rem : ∀ q r → T (r < m) → ModView m (r + q * m)

isPos : ℕ → Bool
isPos 0 = false
isPos _ = true

lem3 : (r m : ℕ) -> T (r < suc m) -> T (m < r) -> ⊥
lem3 zero m p1 ()
lem3 (suc r) zero () p2
lem3 (suc r) (suc m) p1 p2 = lem3 r m p1 p2

lem4 : (q r m : ℕ) -> r ≡ m -> r + q * m ≡ suc q * m
lem4 q r m p = subst (λ x -> x + q * m ≡ suc q * m) (sym p) refl

mod-view : (n m : ℕ) →  T (isPos m) → ModView m n
mod-view n 0 ()
mod-view 0 (suc m) tt  = quot-rem 0 0 tt
mod-view (suc n) (suc m) tt with mod-view n (suc m) tt
-- Проверка r + 1 == m, если да то надо менять q, если нет то r. Третий вариант, а именно r > m невозможен
mod-view (suc .(r + q * suc m)) (suc m) tt | quot-rem q r p with lessity (suc r) (suc m)
mod-view (suc .(r + q * suc m)) (suc m) tt | quot-rem q r p | less .(suc r) .(suc m) x = quot-rem q (suc r) x
mod-view (suc .(r + q * suc m)) (suc m) tt | quot-rem q r p | more .(suc r) .(suc m) x with lem3 r m p x
... | ()
mod-view (suc .(r + q * suc m)) (suc m) tt | quot-rem q r p | eq .(suc r) .(suc m) x =
                  subst (ModView (suc m))
                        (sym (lem4 q (suc r) (suc m) x))
                        (quot-rem (suc q) 0 tt)

div : ℕ → (m : ℕ) → T (isPos m) → ℕ
div n zero ()
div n (suc m) p with mod-view n (suc m) tt
div .(r + q * suc m) (suc m) p | quot-rem q r x = q
