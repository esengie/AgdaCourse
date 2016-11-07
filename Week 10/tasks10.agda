{-# OPTIONS --without-K #-}

module tasks10 where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_)
open import lect10

-- 1. Докажите, что (n + m)-элементное множество равно размеченному объединению n- и m-элементного.


open _⊎_

f : (n m : ℕ) → Fin (n + m) -> (Fin n ⊎ Fin m)
f zero m x = inj₂ x
f (suc n) m zero = inj₁ zero
f (suc n) m (suc x) with f n m x
f (suc n) m (suc x) | inj₁ y = inj₁ (suc y)
f (suc n) m (suc x) | inj₂ y = inj₂ y

f-inv : (n m : ℕ) -> (Fin n ⊎ Fin m) -> Fin (n + m)
f-inv n m (inj₁ x) = inject+ _ x
f-inv n m (inj₂ y) = raise n y

f-isBij : (n m : ℕ) -> isBij (f n m)
f-isBij n m = {!   !}

Fin-sum : (n m : ℕ) → Fin (n + m) ≡ (Fin n ⊎ Fin m)
Fin-sum n m = SetExt ((f n m , f-isBij n m))

-- 2. Докажите, что тип равенств между множествами хоть и не является утверждением, но является множеством.

Set-isGpd : (A B : Set) → isSet (A ≡ B)
Set-isGpd = {!  !}

-- 3. Докажите, что аксиома K не выполняется для множеств.

K : ∀ {l} → Set l → Set l
K A = (a : A) (p : a ≡ a) → p ≡ refl

K-is-false : K Set → ⊥
K-is-false k = {!  !}

-- 4. Докажите, что inv является обратным к **.

inv-left : {A : Set} {x y : A} (p : x ≡ y) → inv p ** p ≡ idp
inv-left = {!  !}

inv-right : {A : Set} {x y : A} (p : x ≡ y) → p ** inv p ≡ idp
inv-right = {!  !}

-- 5. Для любого группоида A постройте группу автоморфизмов его элемента a : A.

record Group (A : Set) : Set where
  field
    set : isSet A
    id : A
    _&_ : A → A → A
    ginv : A → A
    assoc : {x y z : A} → (x & y) & z ≡ x & (y & z)
    id-left : {x : A} → id & x ≡ x
    id-right : {x : A} → x & id ≡ x
    ginv-left : {x : A} → ginv x & x ≡ id
    ginv-right : {x : A} → x & ginv x ≡ id

aut : {A : Set} → isGpd A → (a : A) → Group (a ≡ a)
aut = {!  !}

-- 6. Докажите, что множество автоморфизмов 2-х элементного множества состоит из двух элементов.

data Bool₁ : Set₁ where
  true false : Bool₁

aut-Bool : (Bool ≡ Bool) ≡ Bool₁
aut-Bool = {!  !}

-- 7. Докажите, что группа автоморфизмов в общем случае не коммутативна.

_**'_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p **' refl = p

aut-is-not-comm : ((A : Set) (p q : A ≡ A) → p **' q ≡ q **' p) → ⊥
aut-is-not-comm = {!  !}

-- 8. Докажите, что isProp является предикатом.

isProp-isProp : {A : Set} → isProp (isProp A)
isProp-isProp = {!  !}
