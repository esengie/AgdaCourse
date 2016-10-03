module tasks3 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Bool

-- 1. Vec recursively

Vec : Set -> ℕ -> Set
Vec A 0 = ⊤
Vec A (suc n) = A × Vec A n

list : Vec ℕ 3
list = 0 , 1 , 2 , tt

head : {A : Set} {n : ℕ} -> Vec A (suc n) -> A
head (x , _) = x

tail : {A : Set} {n : ℕ} -> Vec A (suc n) -> Vec A n
tail (_ , xs) = xs

-- 2. Vec inductively

-- data List (A : Set) : Set where -- same structure for dif pars
-- want diff structure based on parameter

-- may write like this
data List : Set -> Set where
  nil : {A : Set} -> List A
  cons : {A : Set} -> A -> List A -> List A

data Vec2 (A : Set) (n : ℕ) : Set where -- problem cant return Vec A 0
  nil : Vec2 A n                 -- well nil: T (n == 0) -> Vec n
  cons : A -> Vec2 A n -> Vec2 A n --   cons : {n' : ℕ} -> T (n == suc n') -> A -> Vec A n' -> Vec A n

data Vec3 (A : Set) : ℕ -> Set where -- isomorphic to vec function
  nil :  Vec3 A 0
  cons : {n : ℕ} -> A -> Vec3 A n -> Vec3 A (suc n)

list₀ : Vec3 ℕ 0
list₀ = nil

list₁ : Vec3 ℕ 1
list₁ = cons 10 nil

len : {A : Set} {n : ℕ} -> Vec3 A n -> ℕ
len {A} {n} _ = n

app : {A : Set} {n k : ℕ} -> Vec3 A n -> Vec3 A k -> Vec3 A (n + k)
app nil ys = ys
app (cons x xs) ys = cons x (app xs ys)

-- head n (cons .n x _) -- dot pattern if explicit args

fac : ℕ -> ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

data Foo' : ℕ -> Set where
  foo : {n : ℕ} -> Foo' (suc n)

-- baz' : (n k : ℕ) - xs   k) -> ℕ
-- baz' zero zero = λ ()
-- baz' zero (suc x) = λ _ → x
-- baz' (suc k) x = λ _ → x

-- data Foo (k : ℕ) : Set where
--   foo : (n : ℕ) -> T (k == fac n) -> Foo k
--
-- baz : (n k : ℕ) -> Foo (n + k) -> ℕ
-- baz n k (foo n1 x) = ?

--------------------------------

data Bar : ℕ -> ℕ -> Set where
  bar : (n : ℕ) -> Bar n n

data Fin : ℕ -> Set where
  zero : {n : ℕ} -> Fin (suc n)
  suc : {n : ℕ} -> Fin n -> Fin (suc n)


index : {A : Set} {n : ℕ} -> Vec3 A n -> (k : Fin n) -> A
index (cons x xs) zero = x
index (cons x xs) (suc k) = index xs k

toN : { n : ℕ } -> Fin n -> ℕ
toN zero = zero
toN (suc x) = suc (toN x)









--
