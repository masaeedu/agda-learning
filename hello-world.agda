module hello-world where

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

-- An approach I bungled together for halving even numbers based on the earlier even proof stuff
halve₀ : (n : ℕ) { _ : n even } → ℕ
halve₀ zero = zero
halve₀ (suc (suc n)) { STEP n-even } = halve₀ n { n-even }

-- A different approach using a predicate
isEven : ℕ → Set
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

halve₁ : ∀ n { _ : isEven n } → ℕ
halve₁ zero = zero
halve₁ (suc (suc n)) { n-even } = halve₁ n { n-even }
