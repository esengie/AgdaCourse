module lect01 where

-- 1. Bool, not, ||, if then else
data Bool : Set where
  true false : Bool

not : Bool -> Bool
not true = false
not false = true

infix 7 _||_
_||_ : Bool -> Bool -> Bool
true || _ = true
false || x = x

-- Фигурные вс Круглые
if_then_else_ : (A : Set) -> Bool -> A -> A -> A
if_then_else_ a false _ f = f -- kind is the first arg
if_then_else_ a true t _  = t -- {a} if curly

-- 2. Nat, +, *
data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

-- 3. Termination, gcd

{-
_-_ : ℕ → ℕ → ℕ
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

div : ℕ → ℕ → ℕ
div x y = if (x < y) then zero else suc (div (x - y) y)
-}

-- 4. Полиморфизм, id, неявные аргументы

-- 5. Списки, append

-- 6. Пустой и одноэлементный типы

-- 7. Пример утверждений и доказательств, not (not x) == x
