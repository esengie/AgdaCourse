{-# OPTIONS --without-K #-}

module Cantor where

open import Data.Product hiding (∃)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
import Level

open import Trunc

∃ : ∀ {i} {j} (A : Set i) (B : A → Set j) → Set (i Level.⊔ j)
∃ A B = ∥ Σ A B ∥

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

Σ' = Σ
syntax Σ' A (λ x → B) = Σ[ x ∶ A ] B

record hProp : Set₁ where
  constructor prop
  field
    A : Set
    proof : isProp A

isSur : ∀ {i} {j} {A : Set i} {B : Set j} → (A → B) → Set (i Level.⊔ j)
isSur {i} {j} {A} {B} f = (y : B) → ∃[ x ∶ A ] (f x ≡ y)

isInj : ∀ {i} {j} {A : Set i} {B : Set j} → (A → B) → Set (i Level.⊔ j)
isInj {i} {j} {A} {B} f = (x x' : A) → f x ≡ f x' → x ≡ x'

isSet : ∀ {i} → Set i → Set i
isSet A = (x y : A) → isProp (x ≡ y)

-- Теорема Кантора говорит, что для любого множества A мощность множества его подмножеств строго больше, чем мощность A.

-- Множество подмножеств можно определить следующим образом:

Subs : Set → Set₁
Subs A = A → hProp -- предикаты

-- Формально утверждение теоремы Кантора состоит из двух частей:
-- "существует инъекция из A в Subs A" и "не существует сюръекции из A в Subs A".

Cantor₁ = (A : Set) → isSet A → Σ[ f ∶ (A → Subs A) ] (isInj f)
Cantor₂ = (A : Set) (f : A → Subs A) → isSur f -> ⊥  -- f берет у и возвращает предикать! лол

-- Докажите теорему Кантора.
fun : {A : Set} -> isSet A -> A -> Subs A
fun sA x y = prop (x ≡ y) ((λ x₁ y₁ → sA x y x₁ y₁))

lma : {A : Set} -> (sA : isSet A) ->
                   isInj (fun sA)
lma sA x y z with (cong hProp.A (cong-app z y)) | hProp.A (fun sA x y) | hProp.proof (fun sA x y)
lma sA x y z | c | v | w = {!   !}

cantor₁ : Cantor₁
cantor₁ A sA = fun sA , lma sA

-- ⊥-isProp : isProp ⊥
-- ⊥-isProp = λ x ()

⊥-isProp : {A : Set} (x y : A) -> isSet A -> isProp ((x ≡ y) -> ⊥)
⊥-isProp x y sA x1 y1 = {! sA ? ? ? ?  !}


fun2 : {A : Set} -> isSet A -> A -> Subs A
fun2 sA x y = prop (x ≡ y -> ⊥) (⊥-isProp x y sA)

-- cantor₂ : Cantor₂
-- cantor₂ A f y = Trunc-rec h1 h2 (y (λ x → prop ⊥ ⊥-isProp))
--   where h1 : (x y₁ : ⊥) → x ≡ y₁
--         h1 ()
--         h2 : Σ A (λ x → f x ≡ (λ x₁ → prop ⊥ ⊥-isProp)) → ⊥
--         h2 (x , ())






--
