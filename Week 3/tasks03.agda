module tasks03 where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product

vec : Set → ℕ → Set
vec A 0 = ⊤
vec A (suc n) = A × vec A n

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)


-- 1. Реализуйте аналоги функции map для vec и Vec.

mapv : {A B : Set} {n : ℕ} -> (A -> B) -> vec A n -> vec B n
mapv {n = zero} f xs = tt
mapv {n = suc n} f (x , xs) = f x , mapv f xs

mapV : {A B : Set} {n : ℕ} -> (A -> B) -> Vec A n -> Vec B n
mapV f nil = nil
mapV f (cons x xs) = cons (f x) (mapV f xs)

-- 2. Реализуйте аналоги функции zip для vec и Vec.
zipv : {A B : Set} {n : ℕ} -> vec A n -> vec B n -> vec (A × B) n
zipv {n = zero} xs ys = tt
zipv {n = suc n} (x , xs) (y , ys) = ( (x , y) , zipv xs ys)

zipV : {A B : Set} {n : ℕ} -> Vec A n -> Vec B n -> Vec (A × B) n
zipV nil nil = nil
zipV (cons x xs) (cons y ys) = cons (x , y) (zipV xs ys)

-- 3. Функции Fin n → A соответствуют спискам элементов A длины n.
--    Функция, преобразующие Vec A n в Fin n → A была реализована на лекции.
--    Реализуйте обратную функцию.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

-- modi : {A : Set} {n : ℕ} -> (Fin n -> A) -> (Fin n -> A)
-- modi f = coin ( λ x -> f (suc x))  \ x -> f (suc x)


coin : {A : Set} {n : ℕ} → (Fin n → A) → Vec A n
coin {n = 0} f = nil
coin {n = suc n} f = cons (f zero) (coin ( \ x -> f (suc x)))

-- 4. Определите тип матриц и ряд функций над ними.

Mat : Set → ℕ → ℕ → Set
Mat A n m = Vec (Vec A m) n

-- диагональная матрица

formN : {A : Set} → A → {n : ℕ} → Vec A n
formN a {0} = nil
formN a {suc n} = cons a (formN a)

diag : {A : Set} → A → A → {n : ℕ} → Mat A n n
diag a z {0} = nil
-- diag a z {n = 1} = cons (cons a nil) nil
diag a z {suc n} = cons (cons a (formN z {n})) (mapV ( λ x -> cons z x) (diag a z {n}))

-- транспонирование матриц

app : {A : Set} {n : ℕ} -> A × (Vec A n) -> Vec A (suc n)
app (x , xs) = cons x xs

transpose : {A : Set} {n m : ℕ} → Mat A n m → Mat A m n
transpose nil = formN nil
transpose (cons nil xs) = nil
transpose (cons x xs) = mapV app (zipV x (transpose xs))

-- сложение матриц

fun1 : {A : Set} (_+_ : A → A → A) -> A × A -> A
fun1 _+_ (a , b) = a + b

a1 : {A : Set} {n : ℕ} (_+_ : A → A → A) -> (Vec A n) × (Vec A n) -> Vec A n
a1 _+_ (xs , ys) = mapV (fun1 _+_) (zipV xs ys)

add : {A : Set} (_+_ : A → A → A) → {n m : ℕ} → Mat A n m → Mat A n m → Mat A n m
add _+_ M N = mapV (a1 _+_) (zipV M N)

_===='_ : ℕ -> ℕ -> Bool
zero ====' zero = true
zero ====' _ = false
_ ====' zero = false
(suc n) ====' (suc m) = n ====' m

_==='_ : {n : ℕ} → Vec ℕ n → Vec ℕ n → Bool
nil ===' nil = true
(cons x xs) ===' (cons y ys) = (x ====' y) ∧ (xs ===' ys)


_=='_ : {n m : ℕ} → Mat ℕ n m → Mat ℕ n m → Bool
nil ==' nil = true
(cons nil xs) ==' (cons nil ys) = true
(cons x xs) ==' (cons y ys) = (x ===' y) ∧ (xs ==' ys)

test1 : T ((add _+_ (cons (cons 1 (cons 2 (cons 3 nil))) nil)
  (cons (cons 1 (cons 2 (cons 3 nil))) nil)) ==' (cons (cons 2 (cons 4 (cons 6 nil))) nil))
test1 = tt

-- умножение матриц

mul : {A : Set} (_+_ _*_ : A → A → A) → {n m k : ℕ} → Mat A n m → Mat A m k → Mat A n k
mul _+_ _*_ M N = {! !}

-- 5. Определите при помощи индуктивных семейств тип CTree A n бинарных деревьев высоты ровно n с элементами во внутренних узлах.
--    Любое такое бинарное дерево будет полным.

data CTree (A : Set) : ℕ → Set where
  empty  : CTree A 0
  node   : {n : ℕ} -> CTree A n -> CTree A n -> CTree A (suc n)

-- 6. Определите при помощи индуктивных семейств тип Tree A n бинарных деревьев высоты не больше n с элементами во внутренних узлах.

data Tree (A : Set) : ℕ → Set where
  empty : {n : ℕ} -> Tree A n
  node  : {n : ℕ} -> Tree A n -> Tree A n -> Tree A (suc n)

emptyT : Tree ℕ 0
emptyT = empty

-- определите функцию, возвращающую высоту дерева.

max' : {n : ℕ} -> Fin n -> Fin n -> Fin n
max' zero x = x
max' x zero = x
max' (suc x) (suc y) = suc (max' x y)

height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
height zero t = zero
height (suc n) empty = zero
height (suc n) (node t t₁) = suc (max' (height n t) (height n t₁))
