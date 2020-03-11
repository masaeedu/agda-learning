module scratch where

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true = false
not false = true

data _even : ℕ → Set where
  ZERO : zero even
  STEP : ∀ { x } → x even → suc (suc x) even

proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (STEP ZERO)

-- https://oxij.org/note/BrutalDepTypes/

id : { A : Set } → A → A
id a = a

idTest₁ : ℕ → ℕ
idTest₁ = id

idTest₂ : ℕ → ℕ
idTest₂ = id { A = ℕ }

idTest₃ : ℕ → ℕ
idTest₃ = id { A = _ }

const : { A B : Set } → A → B → A
const a _ = a

constTest₀ : ℕ → ℕ → ℕ
constTest₀ = const

data Id (A : Set) : Set where
  pack : A → Id A

unpack₀ : { A : _ } → Id A → A
unpack₀ (pack a) = a

unpack₁ : ∀ { A } → Id A → A
unpack₁ (pack x) = x

unpack₂ : ∀ { A B } → Id A → Id B → A
unpack₂ (pack x) _ = x

data ForAllId A (B : Id A) : Set where

testType₀ = ∀ { A } → Id A → A

testType₁ = { A : _ } → (_ : Id A) → A

if_then_else_ : { A : Set } → Bool → A → A → A
if true  then a else _ = a
if false then _ else b = b

_=ℕ?_ : ℕ → ℕ → Bool
zero  =ℕ? zero  = true
zero  =ℕ? suc n = false
suc n =ℕ? zero  = false
suc n =ℕ? suc m = n =ℕ? m

infix 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n  = n
suc n + n′ = suc (n + n′)

ifthenelseTest₀ : ℕ
ifthenelseTest₀ =
  if (zero + suc zero) =ℕ? zero
  then zero
  else suc (suc zero)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

[_] : { A : Set } → A → List A
[ a ] = a ∷ []

listTest₀ : List ℕ
listTest₀ = []

listTest₁ : List ℕ
listTest₁ = zero ∷ (zero ∷ (suc zero ∷ []))

data ⊥ : Set where

⊥-elim : ∀ { A : Set } → ⊥ → A
⊥-elim ()

⊥-elim₀ : { A : Set } → ⊥ → A
⊥-elim₀ x = ⊥-elim x

record Pair (A B : Set) : Set where
  field
    first  : A
    second : B

fst : ∀ { A B } → Pair A B → A
fst = Pair.first

record ⊤ : Set where

tt : ⊤
tt = record {}

recordTest : Pair ℕ ℕ
recordTest  = record { first = zero; second = zero }

-- Lexer is extremely permissive
⊥-elim‵′ : {A : Set} → ⊥ → A
⊥-elim‵′ ∀x:⊥→-- = ⊥-elim ∀x:⊥→--

-- A weird slapdash approach for halving even numbers based on the earlier even proof stuff
halve₀ : ∀ n { proof : n even } → ℕ
halve₀ zero = zero
halve₀ (suc (suc n)) { STEP n-even } = suc (halve₀ n { n-even })

testHalve₀ : ℕ
testHalve₀ = halve₀ (suc (suc zero)) { proof = STEP ZERO }

-- A different approach using a predicate
isEven : ℕ → Set
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

halve₁ : ∀ n { proof : isEven n } → ℕ
halve₁ zero = zero
halve₁ (suc (suc n)) { proof } = suc (halve₁ n { proof })

testHalve₁ : ℕ
testHalve₁ = halve₁ (suc (suc zero)) { proof = tt }

-- Ok, so then in the Type families and Unification section they end up defining the _even *indexed* data type we had above
-- and showing how to define what is basically halve₀

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀ { n } → A → Vec A n → Vec A (suc n)

-- Can't do this for lists
-- head₀ : ∀ { A } → List A → A
-- head₀ []       = {!!}
-- head₀ (a ∷ as) = a

-- Can do it for Vec
head : ∀ { A n } → Vec A (suc n) → A
head (a ∷ _) = a

-- List concatenation
_++_ : ∀ { A } → List A → List A → List A
[] ++ xs = xs
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_++v_ : ∀ { A n m } → Vec A n → Vec A m → Vec A (n + m)
[] ++v xs = xs
(x ∷ xs) ++v ys = x ∷ (xs ++v ys)

-- Gross n - m that tries to work for m > n
infix 6 _-_
_-_ : ℕ → ℕ → ℕ
zero  - _     = zero
suc n - zero  = suc n
suc n - suc m = n - m

-- A number n is less than another number m if …
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ { m }           → zero  ≤ m     -- n is zero, or …
  s≤s : ∀ { n m } → n ≤ m → suc n ≤ suc m -- n = suc n′, m = suc m′, and n′ ≤ m′

-- Nice subtract that simply rejects usage unless m ≤ n
sub₀ : ∀ n m { _ : m ≤ n } → ℕ
sub₀ n       _       { z≤n }     = n
sub₀ (suc n) (suc m) { s≤s m≤n } = sub₀ n m { m≤n }

infix 4 _≡_
data _≡_ { A : Set } (x : A) : A → Set where
  refl : x ≡ x

foo : suc zero ≡ suc (suc zero) - suc zero
foo = refl

-- TODO: Understand why I can't write that equality type by explicitly quantifying over the last variable

-- I guess there's a simpler version of this.

-- Before we had:
-- data Id (A : Set) : Set where
--   pack : A → Id A

-- but suppose we instead write it as an "indexed datatype"

data Id₁ : Set → Set where
  pack₁ : ∀ { A } → A → Id₁ A

-- is that the same thing?
-- TODO: Find the answer
--
-- @monoidmusician provided an example of modeling any other indexed data type using the equality type (which can be viewed as the "fundamental" indexed type)
data Even' (n : ℕ) : Set where
  ezero' : n ≡ zero → Even' n
  e2succ' : { m : ℕ } → n ≡ suc (suc m) → Even' m → Even' n

data Filter (A : Set) (f : A -> Bool) : Set
  where
  Item : (a : A) { _ : f a ≡ true } → Filter A f

isEven' : ℕ → Bool
isEven' zero = true
isEven' (suc n) = not (isEven' n)

test₁ : Filter ℕ isEven'
test₁ = Item zero { refl }

test₂ : Filter ℕ (λ x → not (isEven' x))
test₂ = Item (suc zero) { refl }
