{-# OPTIONS --without-K #-}

module tasks09 where

open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat

open import Trunc

-- 1. Докажите следующие правила, характеризующие квантор существования.

∃ : (A : Set) (B : A → Set) → Set
∃ A B = ∥ Σ A B ∥

∃-intro : {A : Set} {B : A → Set} → (a : A) → B a → ∃[ x ∶ A ] (B x)
∃-intro a b = ∣ (a , b) ∣

∃-elim : {A : Set} {B : A → Set} {C : Set} → isProp C → ((a : A) → B a → C) → ∃ A B → C
∃-elim prC baC = λ x → Trunc-rec prC (λ x₁ → baC (proj₁ x₁) (proj₂ x₁))  x

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

-- 2. Определите утверждение "натуральные числа существуют".

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

natural-numbers-exist : hProp
natural-numbers-exist = prop ∥ ℕ ∥ trunc

-- 3. Докажите, что функция pred сюръективна.

isSur : {A B : Set} → (A → B) → Set
isSur {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

pred-is-not-sur : isSur pred
pred-is-not-sur = λ y → ∣ ( suc y , refl ) ∣

-- 4. Докажите, что функция suc не сюръективна.

suc-is-not-sur : isSur suc → ⊥
suc-is-not-sur p = Trunc-rec h2 h1 (p 0)
  where h1 : Σ ℕ (λ x → suc x ≡ 0) → ⊥
        h1 (proj₁ , ())
        h2 : (x y : ⊥) → x ≡ y
        h2 ()

-- 5. Пусть f : A → B и g : B → C ─ некоторые функции.
--    Докажите, что если f и g сюръективны, то g ∘ f также сюръективна.
--    Докажите, что если g ∘ f сюръективна, то g также сюръективна.

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

∘-sur : {A B C : Set} (f : A → B) (g : B → C) → isSur f → isSur g → isSur (g ∘ f)
∘-sur f g surf surg = λ y → Trunc-rec (λ x y₁ → trunc x y₁)
                                      (λ x → Trunc-rec
                                             (λ x₁ y₁ → trunc x₁ y₁)
                                             (λ x₁ → ∣ ( proj₁ x₁ , trans (cong g (proj₂ x₁)) (proj₂ x) ) ∣ )
                                             (surf (proj₁ x))) (surg y)

∘-sur' : {A B C : Set} (f : A → B) (g : B → C) → isSur (g ∘ f) → isSur g
∘-sur' {A} {B} {C} f g surComp = λ y → lem y (surComp y)
  where lem : (y : C) -> ∃ A (λ x → g (f x) ≡ y) -> ∃ B (λ x → g x ≡ y)
        lem y sfg = Trunc-rec trunc (λ x → ∣ (f (proj₁ x)) , proj₂ x ∣) sfg

-- ∘-sur' f g surComp = λ y → ∣ Trunc-rec (λ x z → {!   !}) (λ x → (f (proj₁ x)) , proj₂ x) (surComp y) ∣

-- 6. Докажите, что функция является биекцией тогда и только тогда, когда она является инъекцией и сюръекцией.

isInj : {A B : Set} → (A → B) → Set
isInj {A} f = (x y : A) → f x ≡ f y → x ≡ y

isBij : {A B : Set} → (A → B) → Set
isBij {A} {B} f = Σ[ g ∶ (B → A) ] (((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))

isBij-isInj : {A B : Set} (f : A → B) → isBij f → isInj f
isBij-isInj f (finv , proj₂ , proj₃) = λ x y x₁ → trans (sym (proj₂ x)) (trans (cong finv x₁) (proj₂ y))

isBij-isSur : {A B : Set} (f : A → B) → isBij f → isSur f
isBij-isSur f (finv , proj₂ , proj₃) = λ y → ∣ (finv y) , (proj₃ y) ∣

isSet : Set → Set
isSet A = (x y : A) → isProp (x ≡ y)

-- Эта лемма вам может пригодится
sigmaExt : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} (p : a ≡ a') → subst B p b ≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
sigmaExt refl q = cong (_,_ _) q

-- (x y : Σ A B) (x₁ y₁ : x ≡ y) → x₁ ≡ y₁

hlpr1 : {A : Set} {a b c : A} -> a ≡ b -> c ≡ b -> a ≡ c
hlpr1 p1 p2 = trans p1 (sym p2)

isInj-isSur-B-A : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f → (y : B) -> Σ[ x ∶ A ] ( f x ≡ y )
isInj-isSur-B-A {A} sB f inF surF b = proj₁ (Trunc-rec lem (λ x -> x) (surF b)) , proj₂ (Trunc-rec lem (λ x -> x) (surF b))
  where lem : isProp (Σ A (λ z → f z ≡ b))
        lem (x1 , y1) (x2 , y2) with inF x1 x2 (hlpr1 y1 y2)
        lem (x1 , y1) (.x1 , y2) | refl with sB (f x1) b y1 y2
        lem (x1 , y1) (.x1 , .y1) | refl | refl = refl

isInj-isSur-isBij : {A B : Set} → isSet B → (f : A → B) → isInj f → isSur f → isBij f
isInj-isSur-isBij {A} {B} sB f inF surF = (λ y -> proj₁ (isInj-isSur-B-A sB f inF surF y)) ,
 (λ x → lem2 x) ,
 (λ y -> proj₂ (isInj-isSur-B-A sB f inF surF y)) -- proj₂ (isInj-isSur-B-A sA sB f inF surF y)
 where lem2 : (x : A) -> proj₁ (isInj-isSur-B-A sB f inF surF (f x)) ≡ x
       lem2 x with (isInj-isSur-B-A sB f inF surF (f x))
       lem2 x | proj₁ , proj₂ = inF proj₁ x proj₂

-- 7. Докажите, что isBij является утверждением.

postulate
  funExt : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g

func : {B : Set} (f g : B -> B) -> isSet B -> ( (y : B) -> f y ≡ y) ->  ( (y : B) -> g y ≡ y) -> f ≡ g
func f g sB pr1 pr2 = {!   !}

props : {B : Set} (f g : B -> B) -> isSet B -> (x1 : (y : B) -> f y ≡ y) -> (x2 : (y : B) -> f y ≡ y) -> x1 ≡ x2
props = {!   !}

isBij-isProp : {A B : Set} → isSet A → isSet B → (f : A → B) → isProp (isBij f)
isBij-isProp sA sB f (finv1 , x1 , y1) (finv2 , x2 , y2) = ?

-- 8. См. Cantor.agda.






--
