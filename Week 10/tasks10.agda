{-# OPTIONS --without-K #-}

module tasks10 where

open import Data.Nat
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_ ; lift)
open import Function using (_∘_)
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

f-toleft : (n m : ℕ) (x : Fin (n + m)) → f-inv n m (f n m x) ≡ x
f-toleft zero m x = refl
f-toleft (suc n) m zero = refl
f-toleft (suc n) m (suc x) with (f n m x)
f-toleft (suc n) m (suc x) | inj₁ y = cong suc {!    !}
f-toleft (suc n) m (suc x) | inj₂ y = {!   !}

f-toright : (n m : ℕ) (y : Fin n ⊎ Fin m) → f n m (f-inv n m y) ≡ y
f-toright _ m (inj₁ zero) = refl
f-toright (suc n) m (inj₁ (suc x)) with f-toright n m (inj₁ x)
... | v = {! cong suc v  !}
f-toright zero m (inj₂ y) = refl
f-toright (suc n) m (inj₂ y) with f-toright n m (inj₂ y)
... | v = {!   !}

f-isBij : (n m : ℕ) -> isBij (f n m)
f-isBij n m = (f-inv n m) , (f-toleft n m) , f-toright n m

Fin-sum : (n m : ℕ) → Fin (n + m) ≡ (Fin n ⊎ Fin m)
Fin-sum n m = SetExt ((f n m , f-isBij n m))

-- 2. Докажите, что тип равенств между множествами хоть и не является утверждением, но является множеством.
sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} (p : a ≡ a') → subst B p b ≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl q = cong (_,_ _) q

open Lift

-- Технический долг =)
sigma-isSet : {A : Set} {B : A → Set} → isSet A → ((x : A) → isSet (B x)) → isSet (Σ A B)
sigma-isSet pA pB (proj₁ , proj₂) (proj₃ , proj₄) = {!   !}

issetbij' : (A B : Set) -> isSet ((Bij A B))
issetbij' A B = sigma-isSet (SmallTypesAreSets (A -> B)) (λ z -> SmallTypesAreSets _)

issetbij : (A B : Set) -> isSet (Lift (Bij A B))
issetbij A B = {! ?  !}

Set-isGpd : (A B : Set) → isSet (A ≡ B)
Set-isGpd A B =  subst isSet (sym (strong-SetExt)) (issetbij A B) -- Lift (Bij A B) ≡ (A ≡ B) --> isSet left -> isSet Right

-- 3. Докажите, что аксиома K не выполняется для множеств.

K : ∀ {l} → Set l → Set l
K A = (a : A) (p : a ≡ a) → p ≡ refl

K-is-false : K Set → ⊥
K-is-false k = {!  !}

-- 4. Докажите, что inv является обратным к **.

inv-left : {A : Set} {x y : A} (p : x ≡ y) → inv p ** p ≡ idp
inv-left refl = refl

inv-right : {A : Set} {x y : A} (p : x ≡ y) → p ** inv p ≡ idp
inv-right refl = refl

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

open Group

aut : {A : Set} → isGpd A → (a : A) → Group (a ≡ a)
aut gpA a = record
  { set = gpA a a
    ; id = refl
    ; _&_ = _**_
    ; ginv = inv
    ; assoc = λ {x} {y} {z} -> **-assoc x y z
    ; id-left = λ {p} -> idp-left-gr p
    ; id-right = λ {p} -> idp-right p
    ; ginv-left = λ {x} -> inv-left x
    ; ginv-right = λ {x} -> inv-right x
  }

-- 6. Докажите, что множество автоморфизмов 2-х элементного множества состоит из двух элементов.

data Bool₁ : Set₁ where
  true false : Bool₁

lft : Bool -> Bool₁
lft true = true
lft false = false

aut2-f : Bool ≡ Bool -> Bool₁
aut2-f p = lft (≡-fun p true)

aut2-g : Bool₁ -> Bool ≡ Bool
aut2-g true = refl
aut2-g false = SetExt (not , not , not-not , not-not)

rightBool : (y : Bool₁) -> aut2-f (aut2-g y) ≡ y
rightBool true = refl
rightBool false = cong lft ( {!   !})

-- ≡-fun (proj₁ SetUni (not , not , not-not , not-not)) ≡ (f true = false)

leftBool : (x : Bool ≡ Bool) → aut2-g (aut2-f x) ≡ x
leftBool x = {!   !}

aut-Bool : (Bool ≡ Bool) ≡ Bool₁
aut-Bool = SetExt (aut2-f , aut2-g , leftBool , rightBool)

-- 7. Докажите, что группа автоморфизмов в общем случае не коммутативна.

_**'_ : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p **' refl = p

data Three : Set where
  one : Three
  two : Three
  thr : Three

top : Three -> Set
top one = ⊤
top two = ⊤
top thr = ⊥

aut1 : Three -> Three
aut1 one = two
aut1 two = one
aut1 thr = thr

aut-h1 : (x : Three) -> aut1 (aut1 x) ≡ x
aut-h1 one = refl
aut-h1 two = refl
aut-h1 thr = refl

aut2 : Three -> Three
aut2 one = one
aut2 two = thr
aut2 thr = two

aut-h2 : (x : Three) -> aut2 (aut2 x) ≡ x
aut-h2 one = refl
aut-h2 two = refl
aut-h2 thr = refl

-- (aut1 (aut2 one)) == two
-- (aut2 (aut1 one)) == thr

alter : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
alter p refl = p


hlpr2 : alter (SetExt (aut1 , aut1 , aut-h1 , aut-h1)) (SetExt (aut2 , aut2 , aut-h2 , aut-h2)) ≡
       alter (SetExt (aut2 , aut2 , aut-h2 , aut-h2)) (SetExt (aut1 , aut1 , aut-h1 , aut-h1)) ->
    (λ x -> aut1 (aut2 x)) ≡ (λ x -> aut2 (aut1 x))
hlpr2 p = {!   !}

hlpr : SetExt (aut1 , aut1 , aut-h1 , aut-h1) **' SetExt (aut2 , aut2 , aut-h2 , aut-h2) ≡
       SetExt (aut2 , aut2 , aut-h2 , aut-h2) **' SetExt (aut1 , aut1 , aut-h1 , aut-h1) ->
    (λ x -> aut1 (aut2 x)) ≡ (λ x -> aut2 (aut1 x))
hlpr p = {!   !}

aut-is-not-comm : ((A : Set) (p q : A ≡ A) → p **' q ≡ q **' p) → ⊥
aut-is-not-comm f =
  let t = f Three (SetExt (aut1 , aut1 , aut-h1 , aut-h1)) (SetExt (aut2 , aut2 , aut-h2 , aut-h2))
      t1 = hlpr t
      t2 = cong (λ f → f one) t1
  in subst top t2 tt

-- 8. Докажите, что isProp является предикатом.

isProp-isProp : {A : Set} → isProp (isProp A)
isProp-isProp = {!  !}
