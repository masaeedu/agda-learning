module ct.ct where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record relation (a : Set) (b : Set) : Set₁ where
  infix 4 _~_

  field
    _~_ : a → b → Set

record equivalence (a : Set) : Set₁ where
  field
    {{rel}} : relation a a

  open relation rel

  field
    reflexivity  : ∀ { x : a } → x ~ x
    symmetry     : ∀ { x y : a } → x ~ y → y ~ x
    transitivity : ∀ { x y z : a } → y ~ z → x ~ y → x ~ z

open equivalence

propeq : ∀ { a : Set } → equivalence a
propeq = record
  { rel = record { _~_ = _≡_ }
  ; reflexivity = refl
  ; symmetry = symm
  ; transitivity = trans
  }
  where
  symm : { x : Set } { a b : x } → a ≡ b → b ≡ a
  symm refl = refl

  trans : { x : Set } { a b c : x } → b ≡ c → a ≡ b → a ≡ c
  trans refl refl = refl

exteq : ∀ { a b : Set } → equivalence (a → b)
exteq = record
  { rel = record { _~_ = _~_ }
  ; reflexivity = refl
  ; symmetry = symm
  ; transitivity = trans
  }
  where
  _~_ : { a b : Set } → (a → b) → (a → b) → Set
  _~_ f g = ∀ { x } → f x ≡ g x

  symm : { a b : Set } { f g : a → b } → f ~ g → g ~ f
  symm e { x } = symmetry propeq (e { x })

  trans : { a b : Set } { f g h : a → b } → g ~ h → f ~ g → f ~ h
  trans gh fg { x } = transitivity propeq (gh { x }) (fg { x })

record cat { k : Set₁ } (_⇒_ : k → k → Set) (eq : ∀ { a b : k } → equivalence (a ⇒ b)) : Set₁
  where
  field
    id  : { a : k } → a ⇒ a
    _∘_ : { a b c : k } → b ⇒ c → a ⇒ b → a ⇒ c

    lunit : ∀ { a b }     { x : a ⇒ b }                             → relation._~_ (rel eq) (id ∘ x) x
    runit : ∀ { a b }     { x : a ⇒ b }                             → relation._~_ (rel eq) (x ∘ id) x
    assoc : ∀ { a b c d } { x : c ⇒ d } { y : b ⇒ c } { z : a ⇒ b } → relation._~_ (rel eq) (x ∘ (y ∘ z)) ((x ∘ y) ∘ z)

_⇒_ : Set → Set → Set
a ⇒ b = a → b

cat⇒ : cat _⇒_ exteq
cat⇒ = record
  { id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; lunit = refl
  ; runit = refl
  ; assoc = refl
  }

data bool : Set₁
  where
  ⊤ : bool
  ⊥ : bool

data _⊃_ : bool → bool → Set
  where
  tt : ⊤ ⊃ ⊤
  ff : ⊥ ⊃ ⊥
  ft : ⊥ ⊃ ⊤

cat⊃ : cat _⊃_ propeq
cat⊃ = record
  { id = id⊃
  ; _∘_ = _∘⊃_
  ; lunit = lunit⊃
  ; runit = runit⊃
  ; assoc = assoc⊃
  }
  where
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
