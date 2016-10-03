module tasks04 where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Relation.Nullary
open import Data.Sum
open import Data.Vec hiding (reverse) renaming (_++_ to _+V+_)
open import Data.List hiding (reverse) renaming (_++_ to _+L+_)
open import Relation.Binary.PropositionalEquality hiding (sym; trans; cong; cong₂)


-- 2. Определите симметричность, транзитивность и конгруэнтность при помощи паттерн матчинга.

sym : {A : Set} {a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : {A : Set} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

cong : {A B : Set} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

-- 1. Доказать следующий факт.

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

_==_ : (ℕ → ℕ) → (ℕ → ℕ) → Set
f == g = (x : ℕ) → f x ≡ g x


D : ℕ → Set
D zero = ⊥
D (suc _) = ⊤

infix 1 _=='_
_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' suc _ = false
suc _ ==' 0 = false
suc x ==' suc y = x ==' y

≡-== : {x y : ℕ} → x ≡ y → T (x ==' y)
≡-== {zero} {zero} p = tt
≡-== {zero} {(suc y)} ()
≡-== {(suc x)} {zero} p = subst D p tt
≡-== {(suc x)} {(suc y)} p = ≡-== {x} {y} (cong pred p)

lem : fac == suc → ⊥
lem p = ≡-== ( p 10 )

-- 3. Определите конгруэнтность для функций двух аргументов через subst.

cong₂ : {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f {a} {a'} {b = b} p1 p2 = subst (λ x → f a b ≡ f a' x) p2 (subst (λ x → f a b ≡ f x b) p1 refl)

-- 4. Докажите дистрибутивность умножения над сложением для натуральных чисел.

open ≡-Reasoning

+-assoc : (x : ℕ) {y z : ℕ} → (x + y) + z ≡ x + (y + z)
+-assoc zero = refl
+-assoc (suc x) = cong suc (+-assoc x)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (sym (+-comm x y))) (+-comm (suc x) y)))

distr : (n m k : ℕ) → n * (m + k) ≡ n * m + n * k
distr zero m k = refl
distr (suc n) m k =
  (begin
    m + k + n * (m + k)
  ≡⟨ cong (λ x -> m + k + x) (distr n m k) ⟩
    m + k + (n * m + n * k)
  ≡⟨ +-assoc m ⟩
    m + (k + (n * m + n * k))
  ≡⟨ cong (λ x -> m + x)
    (begin
      k + (n * m + n * k)
    ≡⟨ sym (+-assoc k) ⟩
      (k + n * m) + n * k
    ≡⟨ cong (λ x -> x + n * k)
      (begin
        k + n * m
        ≡⟨ +-comm k (n * m) ⟩
        n * m + k
        ∎) ⟩
      n * m + k + n * k
      ≡⟨ +-assoc (n * m) ⟩
      n * m + (k + n * k)
    ∎) ⟩
    m + (n * m + (k + n * k))
  ≡⟨ sym (+-assoc m) ⟩
    m + n * m + (k + n * k)
  ∎)

-- 5. Докажите следующее утверждение.

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs +L+ x ∷ []

[]not : {A : Set} (xs : List A) -> xs +L+ [] ≡ xs
[]not [] = refl
[]not (x ∷ xs) = cong (_∷_ x) ([]not xs)

++assoc : {A : Set} (xs ys zs : List A) -> (xs +L+ ys) +L+ zs ≡ xs +L+ (ys +L+ zs)
++assoc [] ys zs = refl
++assoc (x ∷ xs) ys zs = cong (_∷_ x) (++assoc xs ys zs)

reverse- : {A : Set} (xs ys : List A) → reverse (reverse xs +L+ ys) ≡ reverse ys +L+ xs
reverse- [] ys = sym ([]not (reverse ys))
reverse- (x ∷ xs) ys = begin
  reverse ((reverse xs +L+ x ∷ []) +L+ ys)
  ≡⟨ cong reverse (++assoc (reverse xs) (x ∷ []) ys) ⟩
  reverse (reverse xs +L+ (x ∷ []) +L+ ys)
  ≡⟨ reverse- xs ((x ∷ []) +L+ ys) ⟩
  (reverse ys +L+ x ∷ []) +L+ xs
  ≡⟨ ++assoc (reverse ys) (x ∷ []) xs ⟩
  reverse ys +L+ x ∷ xs
  ∎

reverse-inv : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-inv [] = refl
reverse-inv (x ∷ xs) = reverse- xs (x ∷ [])

-- 6. Докажите следующее утверждение.

reverse-append : {A : Set} (xs ys : List A) → reverse (xs +L+ ys) ≡ reverse ys +L+ reverse xs
reverse-append [] ys = sym ([]not (reverse ys))
reverse-append (x ∷ xs) ys =
  begin
      reverse (xs +L+ ys) +L+ x ∷ []
      ≡⟨ cong (λ lst -> lst +L+ (x ∷ [])) (reverse-append xs ys) ⟩
      (reverse ys +L+ reverse xs) +L+ x ∷ []
      ≡⟨ ++assoc (reverse ys) (reverse xs) (x ∷ []) ⟩
      reverse ys +L+ (reverse xs +L+ x ∷ [])
  ∎

-- 7. Докажите, что [] является нейтральным элементом для ++.

[]-is-neutral : {A : Set} {n : ℕ} (xs : Vec A n) → subst (Vec A) (+-comm n 0) (xs +V+ []) ≡ xs
[]-is-neutral [] = refl
[]-is-neutral {A} {n = suc n} (x ∷ xs) = trans (lemma x (+-comm n 0) (xs +V+ [])) (cong (_∷_ x) ([]-is-neutral xs))
  where
    lemma : (x : A) {n m : ℕ} (p : n ≡ m) (xs : Vec A n) ->
      subst (Vec A) (cong suc p) (x ∷ xs) ≡ x ∷ subst (Vec A) p xs
    lemma x₁ refl xs₁ = refl


-- 8. Определите reverse для Vec через аккумулятор.

lemma₁ : (n m : ℕ) -> suc (n + m) ≡ n + suc m
lemma₁ zero m = refl
lemma₁ (suc n) m = cong suc (lemma₁ n m)

reverse' : {A : Set} {n m : ℕ} -> Vec A n -> Vec A m -> Vec A (n + m)
reverse' {A} {n} acc [] = subst (Vec A) (+-comm 0 n) acc
reverse' {A} {n} {suc m} acc (x ∷ xs) = subst (Vec A) (lemma₁ n m) (reverse' (x ∷ acc) xs)

rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev {A} {n} xs = (reverse' [] xs)

-- 9. Докажите, что [] не равно x ∷ xs при помощи паттер матчинга.
List-diff : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff _ [] ()
List-diff _ (x₁ ∷ xs) ()

-- 10. Докажите, что [] не равно x ∷ xs при помощи subst.
pat : {A : Set} -> List A -> Set
pat [] = ⊤
pat (x ∷ xs) = ⊥

List-diff' : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff' _ _ p = subst pat p tt



--
