module ct.ct where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record relation (a b : Set) : Set₁ where
  infix 4 _~_

  field
    _~_ : a → b → Set

open relation ⦃ ... ⦄

record equivalence (a : Set) : Set₁ where
  field
    ⦃ rel ⦄ : relation a a

  open relation rel public renaming (_~_ to _≈_)

  field
    reflexivity  : ∀ { x } → x ≈ x
    symmetry     : ∀ { x y } → x ≈ y → y ≈ x
    transitivity : ∀ { x y z } → y ≈ z → x ≈ y → x ≈ z

open equivalence ⦃ ... ⦄

record category { k : Set₁ } (_⇒_ : k → k → Set) : Set₁
  where
  field
    id  : ∀ { a } → a ⇒ a
    _∘_ : ∀ { a b c } → b ⇒ c → a ⇒ b → a ⇒ c

  field
    ⦃ hom ⦄ : ∀ { a b } → equivalence (a ⇒ b)

  field
    lunit : ∀ { a b }     { x : a ⇒ b }                             → id ∘ x ≈ x
    runit : ∀ { a b }     { x : a ⇒ b }                             → x ∘ id ≈ x
    assoc : ∀ { a b c d } { x : c ⇒ d } { y : b ⇒ c } { z : a ⇒ b } → x ∘ (y ∘ z) ≈ (x ∘ y) ∘ z

open category ⦃ ... ⦄

-- {{{ Relations

nrel : { a : Set } → relation a a
nrel = record { _~_ = _≡_ }

funrel : { a b : Set } → relation b b → relation (a → b) (a → b)
funrel v = record { _~_ = let instance b = v in λ f g → ∀ { x } → f x ~ g x }

-- }}}

-- {{{ Equivalences

-- Equivalence modulo normalization
neq : ∀ { a } → equivalence a
neq = record
  { reflexivity = refl
  ; symmetry = symm
  ; transitivity = trans
  }
  where
  instance p = nrel

  symm : { x : Set } { a b : x } → a ≡ b → b ≡ a
  symm refl = refl

  trans : { x : Set } { a b c : x } → b ≡ c → a ≡ b → a ≡ c
  trans refl refl = refl

-- Extensional equivalence given some notion of codomain equivalence
extensional : ∀ { a b : Set } → equivalence b → equivalence (a → b)
extensional e = record
  { rel = funrel rel
  ; reflexivity = reflexivity
  ; symmetry = λ ab → symmetry ab
  ; transitivity = λ bc ab → transitivity bc ab
  }
  where
  instance
    eq = e

-- }}}

-- {{{ Categories

-- The category of typed functions
_⇒_ : Set → Set → Set
a ⇒ b = a → b

cat⇒ : category _⇒_
cat⇒ = record
  { hom = extensional neq
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; lunit = refl
  ; runit = refl
  ; assoc = refl
  }

-- The preorder of booleans
data bool : Set₁
  where
  ⊤ : bool
  ⊥ : bool

data _⊃_ : bool → bool → Set
  where
  tt : ⊤ ⊃ ⊤
  ff : ⊥ ⊃ ⊥
  ft : ⊥ ⊃ ⊤

cat⊃ : category _⊃_
cat⊃ = record
  { hom = neq
  ; id = id⊃
  ; _∘_ = _∘⊃_
  ; lunit = lunit⊃
  ; runit = runit⊃
  ; assoc = assoc⊃
  }
  where
  instance pe = neq

  id⊃ : ∀ { a } → a ⊃ a
  id⊃ { ⊤ } = tt
  id⊃ { ⊥ } = ff

  _∘⊃_ : ∀ { a b c } → b ⊃ c → a ⊃ b → a ⊃ c
  tt ∘⊃ tt = tt
  tt ∘⊃ ft = ft
  ff ∘⊃ ff = ff
  ft ∘⊃ ff = ft

  lunit⊃ : ∀ { a b } { x : a ⊃ b } → id⊃ ∘⊃ x ≡ x
  lunit⊃ {_} {_} {tt} = refl
  lunit⊃ {_} {_} {ft} = refl
  lunit⊃ {_} {_} {ff} = refl

  runit⊃ : ∀ { a b } { x : a ⊃ b } → x ∘⊃ id⊃ ≡ x
  runit⊃ {_} {_} {tt} = refl
  runit⊃ {_} {_} {ft} = refl
  runit⊃ {_} {_} {ff} = refl

  assoc⊃ : ∀ { a b c d } { x : c ⊃ d } { y : b ⊃ c } { z : a ⊃ b } → x ∘⊃ (y ∘⊃ z) ≡ (x ∘⊃ y) ∘⊃ z
  assoc⊃ {_} {_} {_} {_} {tt} {tt} {tt} = refl
  assoc⊃ {_} {_} {_} {_} {tt} {tt} {ft} = refl
  assoc⊃ {_} {_} {_} {_} {tt} {ft} {ff} = refl
  assoc⊃ {_} {_} {_} {_} {ft} {ff} {ff} = refl
  assoc⊃ {_} {_} {_} {_} {ff} {ff} {ff} = refl

-- }}}
