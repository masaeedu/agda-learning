{-# OPTIONS --cubical #-}
module ct.ct where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record cat { ℓ₁ ℓ₂ } { k : Set ℓ₁ } (p : k → k → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂)
  where
  field
    id  : { a : k } → p a a
    _∘_ : { a b c : k } → p b c → p a b → p a c

    lunit : ∀ { a b }     { x : p a b }                             → id ∘ x ≡ x
    runit : ∀ { a b }     { x : p a b }                             → x ∘ id ≡ x
    assoc : ∀ { a b c d } { x : p c d } { y : p b c } { z : p a b } → x ∘ (y ∘ z) ≡ (x ∘ y) ∘ z

_⇒_ : Set → Set → Set
a ⇒ b = a → b

cat_⇒ : cat _⇒_
cat.id    cat_⇒ x = x
cat._∘_   cat_⇒ f g x = f (g x)
cat.lunit cat_⇒ = ?
cat.runit cat_⇒ = ?
cat.assoc cat_⇒ = ?

data bool { ℓ } : Set ℓ where
  ⊤ : bool
  ⊥ : bool

data _⊃_ { ℓ } : bool { ℓ } → bool { ℓ } → Set ℓ where
  tt : ⊤ ⊃ ⊤
  ff : ⊥ ⊃ ⊥
  ft : ⊥ ⊃ ⊤

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

cat⊃ : cat _⊃_
cat⊃ = record { id = id⊃; _∘_ = _∘⊃_; lunit = lunit⊃; runit = runit⊃; assoc = assoc⊃ }
