module tasks05 where

open import Data.Nat
open import Data.List
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Data.Char
open import Data.String hiding (_++_)

-- 1. Используя тип List, определите тип данных (через зависимые записи) списков длины n (число должно быть параметром записи).
--    Реализуйте для такого типа функции head и tail.

record ListN {A : Set} {n : ℕ} : Set where
  constructor listN
  field
    lst : List A
    constraint : length (lst) ≡ n

head : {A : Set} {n : ℕ} -> ListN {A} {suc n} -> A
head (listN [] ())
head (listN (x ∷ lst) constraint) = x

tail : {A : Set} {n : ℕ} -> ListN {A} {suc n} -> ListN {A} {n}
tail (listN [] ())
tail (listN (x ∷ lst) con) = listN lst (cong pred con)


-- 2. Определите тип (через зависимые записи) четных натуральных чисел.
--    Определите функцию деления на 2.

even : ℕ -> Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

record Evenℕ : Set where
  constructor evenN
  field
    n : ℕ
    ct : T (even n)

div2 : Evenℕ → ℕ
div2 (evenN zero ct) = 0
div2 (evenN (suc zero) ())
div2 (evenN (suc (suc n)) ct) = 1 + div2 (evenN n ct)

-- 3. Постройте структуру моноида на типе натуральных чисел (т.е. нужно сконструировать элемент соответствующей записи).

record Monoid (A : Set) : Set₁ where
  field
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

+-assoc : (x : ℕ) {y z : ℕ} → (x + y) + z ≡ x + (y + z)
+-assoc zero = refl
+-assoc (suc x) = cong suc (+-assoc x)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (sym (+-comm x y))) (+-comm (suc x) y)))


ℕ-Monoid : Monoid ℕ
ℕ-Monoid = record { id = 0
                  ; _#_ = _+_
                  ; assoc = λ x y z → +-assoc x
                  ; id-left = λ x → refl
                  ; id-right = λ x → +-comm x 0
                  }

-- 4. Напишите тип монады (через зависимые записи).
--    Элементы этого типа должны удовлетворять всем законом монад.

record Monad (M : Set → Set) : Set₁ where
  field
    return : {A : Set} -> A -> M A
    _>>=_ : {A B : Set} -> M A → (A -> M B) → M B

    left-id : {A B : Set} {a : A} {b : B} -> (f : A -> M B) -> return a >>= f ≡ f a
    right-id : {A : Set} {a : A} -> (m : M A) -> m >>= return ≡ m
    assoc : {A B C : Set} {a : A} {b : B} (m : M A) -> (f : A -> M B) -> (g : B -> M C) ->
      (m >>= f) >>= g ≡ m >>= (λ x -> f x >>= g)


-- 5. Определите тип данных Maybe, сконструируйте структуру функтора и монады на этом типе.

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) → fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A -> Maybe A

mfmap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mfmap f Nothing = Nothing
mfmap f (Just x) = Just (f x)

mfmap-id : {A : Set} (a : Maybe A) → mfmap (λ x → x) a ≡ a
mfmap-id Nothing = refl
mfmap-id (Just x) = refl

mfmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : Maybe A) → mfmap (λ x → g (f x)) a ≡ mfmap g (mfmap f a)
mfmap-comp f g Nothing = refl
mfmap-comp f g (Just x) = refl

Maybe-Functor : Functor Maybe
Maybe-Functor = record { fmap = mfmap
                        ; fmap-id = mfmap-id
                        ; fmap-comp = mfmap-comp
                       }

mret : {A : Set} -> A -> Maybe A
mret = Just

_m>>=_ : {A B : Set} -> Maybe A → (A -> Maybe B) → Maybe B
Nothing m>>= f = Nothing
Just x m>>= f = f x

mright-id : {A : Set} {a : A} -> (m : Maybe A) -> (m m>>= mret) ≡ m
mright-id Nothing = refl
mright-id (Just x) = refl


massoc : {A B C : Set} {a : A} {b : B} -> (m : Maybe A) -> (f : A -> Maybe B) -> (g : B -> Maybe C) ->
  (m m>>= f) m>>= g ≡ m m>>= (λ x -> f x m>>= g)
massoc Nothing f g = refl
massoc (Just x) f g = refl

Maybe-Monad : Monad Maybe
Maybe-Monad = record { return = mret
                      ; _>>=_ = _m>>=_
                      ; left-id = λ f → refl
                      ; right-id = λ {A} {a} -> mright-id {A} {a}
                      ; assoc = λ {A} {B} {C} {a} {b} -> massoc {A} {B} {C} {a} {b} }

open Monad

stupidFunc : {B : Set -> Set} {m : Monad B} -> B ℕ -> B ℕ
stupidFunc {m = m} a = (_>>=_ m) a ((λ x -> (Monad.return m) (x + 3)))

lol : Maybe ℕ
lol = stupidFunc {Maybe} {Maybe-Monad} (Just 3)


open Monoid

data Writer (W : Set) {m : Monoid W} (A : Set) : Set where
  runWriter : A × W -> Writer W A

>>helper : {W : Set} {m : Monoid W} {B : Set} -> Writer W {m} B -> W -> Writer W {m} B
>>helper {m = m} (runWriter (b , w')) w = runWriter (b , (_#_ m) w w')

_w>>=_ : {W : Set} {m : Monoid W} {A B : Set} -> Writer W {m} A → (A -> Writer W {m} B) → Writer W {m} B
_w>>=_ {W = W} {m = m} {B = B} (runWriter (a , w)) f = >>helper (f a) w

wleft-id : {W : Set} {m : Monoid W} {B : Set} (b : Writer W {m} B) ->
    >>helper b (id m) ≡ b
wleft-id {m = m} (runWriter (a , w)) = cong ( λ x -> runWriter (a , x)) (id-left m w)

wright-id : {W : Set} {m : Monoid W} {A : Set} {monad : Writer W {m} A} -> (monad w>>= (λ x → runWriter (x , id m))) ≡ monad
wright-id {m = m} {monad = runWriter (a , w)} = cong ( λ x -> runWriter (a , x)) (id-right m w)

wassocHelperHelper : {W : Set} {m : Monoid W} {A B C : Set} {a : A} {b : B} {w w' : W} ->
  (monad : Writer W {m} C) ->
  >>helper monad ((m # w) w') ≡ >>helper (>>helper monad w') w
wassocHelperHelper {m = m} {w = w} {w' = w'} (runWriter (a , w'')) =
  cong (λ x -> runWriter (a , x)) (Monoid.assoc m w w' w'')

wassocHelper : {W : Set} {m : Monoid W} {A B C : Set} {a : A} {b : B} {w : W} ->
  (monad : Writer W {m} B) -> (g : B -> Writer W {m} C) ->
  (>>helper monad w w>>= g) ≡ >>helper (monad w>>= g) w
wassocHelper {W} {m} {A} {B} {C} {a} {b} {w} (runWriter (a' , w')) g =
  wassocHelperHelper {W} {m} {A} {B} {C} {a} {b} {w} (g a')

wassoc : {W : Set} {m : Monoid W} {A B C : Set} {a : A} {b : B} ->
  (monad : Writer W {m} A) -> (f : A -> Writer W {m} B) -> (g : B -> Writer W {m} C) ->
  (monad w>>= f) w>>= g ≡ monad w>>= (λ x -> f x w>>= g)
wassoc {W} {m} {A} {B} {C} {a} {b} (runWriter (a' , w)) f g = wassocHelper {W} {m} {A} {B} {C} {a} {b} (f a') g

-- Writer-Monad : {B : Set} {m : Monoid B} -> Monad (λ x -> x × B)
Writer-Monad : {W : Set} {m : Monoid W} -> Monad (Writer W {m})
Writer-Monad {W} {m} = record { return = λ x -> runWriter (x , id m)
                        ; _>>=_ = _w>>=_
                        ; left-id = λ {A} {B} {a} f → wleft-id (f a)
                        ; right-id = λ m₁ → wright-id
                        ; assoc = λ {A} {B} {C} {a} {b} -> wassoc {W} {m} {A} {B} {C} {a} {b} }

-- 6. Реализуйте sscanf.

data FmtData : Set where
  num : FmtData
  bool : FmtData

FmtRes : List FmtData -> Set
FmtRes [] = List Char
FmtRes (num ∷ xs) = ℕ × FmtRes xs
FmtRes (bool ∷ xs) = Bool × FmtRes xs

string-toFmtData : List Char → List FmtData
string-toFmtData [] = []
string-toFmtData ('%' ∷ 'd' ∷ xs) = num ∷ string-toFmtData xs
string-toFmtData ('%' ∷ 'b' ∷ xs) = bool ∷ string-toFmtData xs
string-toFmtData (x ∷ xs) = string-toFmtData xs

sscanf : List Char -> (fmt : List Char) -> FmtRes (string-toFmtData fmt)
sscanf xs [] = []
sscanf xs (x ∷ fmt) = {!   !}


-- sscanf "" "%d"





--
