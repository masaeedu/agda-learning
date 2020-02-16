module ct.ct where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record relation (a b : Set) : Set₁ where
  infix 4 _~_

  field
    _~_ : a → b → Set

record equivalence (a : Set) : Set₁ where
  field
    ⦃ rel ⦄ : relation a a

  open relation rel public

  field
    reflexivity  : ∀ { x } → x ~ x
    symmetry     : ∀ { x y } → x ~ y → y ~ x
    transitivity : ∀ { x y z } → y ~ z → x ~ y → x ~ z

open equivalence ⦃ ... ⦄

record category { k : Set₁ } (_⇒_ : k → k → Set) : Set₁
  where
  field
    id  : ∀ { a } → a ⇒ a
    _∘_ : ∀ { a b c } → b ⇒ c → a ⇒ b → a ⇒ c

  field
    ⦃ hom ⦄ : ∀ { a b } → equivalence (a ⇒ b)

  field
    lunit : ∀ { a b }     { x : a ⇒ b }                             → id ∘ x ~ x
    runit : ∀ { a b }     { x : a ⇒ b }                             → x ∘ id ~ x
    assoc : ∀ { a b c d } { x : c ⇒ d } { y : b ⇒ c } { z : a ⇒ b } → x ∘ (y ∘ z) ~ (x ∘ y) ∘ z

open category ⦃ ... ⦄

-- {{{ Relations

proprel : { a : Set } → relation a a
proprel = record { _~_ = _≡_ }

funrel : { a b : Set } → relation (a → b) (a → b)
funrel = record { _~_ = λ f g → ∀ { x } → f x ≡ g x }

-- }}}

-- {{{ Equivalences

propeq : ∀ { a } → equivalence a
propeq = record
  { reflexivity = refl
  ; symmetry = symm
  ; transitivity = trans
  }
  where
  instance p = proprel

  symm : { x : Set } { a b : x } → a ≡ b → b ≡ a
  symm refl = refl

  trans : { x : Set } { a b c : x } → b ≡ c → a ≡ b → a ≡ c
  trans refl refl = refl

exteq : ∀ { a b : Set } → equivalence (a → b)
exteq = record
  { rel = record { _~_ = _~_ }
  ; reflexivity = reflexivity
  ; symmetry = symmetry
  ; transitivity = transitivity
  }
  where
  instance
    fr = funrel
    pe = propeq

-- }}}

-- {{{ Categories

_⇒_ : Set → Set → Set
a ⇒ b = a → b

cat⇒ : category _⇒_
cat⇒ = record
  { id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; lunit = refl
  ; runit = refl
  ; assoc = refl
  }
  where
  instance ee = exteq

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
  { id = id⊃
  ; _∘_ = _∘⊃_
  ; lunit = lunit⊃
  ; runit = runit⊃
  ; assoc = assoc⊃
  }
  where
  instance pe = propeq

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
