module lec4 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding (subst; sym; trans; cong)

open ≡-Reasoning

-- data _≡_ {A : Set} (a : A): A -> Set where
--   refl : a ≡ a -- second a is a parameter

-- data _≡_ {A : Set} : A -> A -> Set where
--   refl : {a : A} -> a ≡ a

-- data _≡_ : {A : Set} -> A -> A -> Set where
--   refl : {A : Set} {a : A} -> a ≡ a


fac : ℕ -> ℕ
fac 0 = 1
fac (suc n) = (suc n) * fac n

_=='_ : ℕ -> ℕ -> Bool
0 ==' 0 = true
0 ==' suc n = false
suc n ==' 0 = false
suc n ==' suc m = n ==' m

test1 : T (fac 5 ==' 120)
test1 = tt

-----------------------------

subst : {A : Set} (B : A -> Set) {a a' : A} -> a ≡ a' -> B a -> B a'
subst B refl b = b

sym : {A : Set} {a a' : A} -> a ≡ a' -> a' ≡ a
sym {a = a} p = subst (λ x -> x ≡ a) p refl

trans : {A : Set} {a a' a'' : A} -> a ≡ a' -> a' ≡ a'' -> a ≡ a''
trans {a = a} p q = subst (λ x -> a ≡ x) q p

cong : {A B : Set} (f : A -> B) {a a' : A} -> a ≡ a' -> f a ≡ f a'
cong f {a} p = subst (λ x -> f a ≡ f x) p refl

----------------------------

assoc1 : (x y z : ℕ) -> T (((x + y) + z) ==' (x + (y + z)))
assoc1 x y z = {!   !}

assoc2 : (x y z : ℕ) -> (((x + y) + z) ≡ (x + (y + z)))
assoc2 zero y z = refl
assoc2 (suc x) y z = cong suc (assoc2 x y z)

com2 : (x y : ℕ) -> (x + y) ≡ (y + x)
com2 zero zero = refl
com2 zero (suc y) = cong suc (com2 0 y)
com2 (suc x) zero = cong suc (com2 x 0)
com2 (suc x) (suc y) = cong suc (trans (com2 x (suc y))
  (trans ((cong suc (com2 y x))) (com2 (suc x) y)))

com3 : (x y : ℕ) -> (x + y) ≡ (y + x)
com3 zero zero = refl
com3 zero (suc y) = cong suc (com3 0 y)
com3 (suc x) zero = cong suc (com3 x 0)
com3 (suc x) (suc y) = cong suc (
  begin
    x + suc y
  ≡⟨ com3 x (suc y) ⟩         -- _≡⟨_⟩_
    suc y + x
    ≡⟨ refl ⟩
    suc (y + x)
    ≡⟨ cong suc (sym (com3 x y)) ⟩
      suc (x + y)
      ≡⟨ com3 (suc x) y ⟩
        y + suc x
  ∎ )


-- rev : { A : Set} { n : ℕ } -> Vec A n -> Vec A n
-- rev [] = []
-- rev {A} {n} (x ∷ xs) = subst (Vec A) (com3 n 1) (rev xs ++ x ∷ [])

-- rev (n + 1)
-- want rev (1 + n)


-- ++assoc : {A : Set} {n m k : ℕ} (xs : Vec A n)
--   (ys : Vec A m) (zs : Vec A k) -> (xs ++ ys) ++ zs ≡ xs ++ (ys + zs)
-- ++assoc = ?

-- Works!
-- ++assoc : {A : Set} {n m k : ℕ} (xs : Vec A n)
--   (ys : Vec A m) (zs : Vec A k) -> subst (Vec A) (assoc2 n m k) (xs ++ ys) ++ zs ≡ xs ++ (ys + zs)
-- ++assoc = ?

-- Works!
-- ++assoc : {A : Set} {n m k : ℕ} (xs : Vec A n)
--   (ys : Vec A m) (zs : Vec A k) -> subst (Vec A) (assoc2 n m k) (xs ++ ys) ++ zs ≡ xs ++ (ys + zs)
-- ++assoc = ?






--
