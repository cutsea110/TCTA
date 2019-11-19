module Category where

open import Level
open import Relation.Binary.Core

record IsCategory {c₁ c₂ ℓ : Level} (Obj : Set c₁)
                  (Hom : Obj → Obj → Set c₂)
                  (_≈_ : {A B : Obj} → Rel (Hom A B) ℓ)
                  (_∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C)
                  (Id  : {A : Obj} → Hom A A) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
       field
         isEquivalence : {A B : Obj} → IsEquivalence {c₂} {ℓ} {Hom A B} _≈_
         identityL : {A B : Obj} → {f : Hom A B} → (Id ∘ f) ≈ f
         identityR : {A B : Obj} → {f : Hom A B} → (f ∘ Id) ≈ f
         ∘-resp-≈ : {A B C : Obj} {f g : Hom A B} {h i : Hom B C} → f ≈ g → h ≈ i → (h ∘ f) ≈ (i ∘ g)
         associative : {A B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom A B} → (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)

record Category c₁ c₂ ℓ : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  infixr 9 _∘_
  infix  4 _≈_
  field
    Obj : Set c₁
    Hom : Obj → Obj → Set c₂
    _∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    _≈_ : {A B : Obj} → Rel (Hom A B) ℓ
    Id  : {A : Obj} → Hom A A
    isCategory : IsCategory Obj Hom _≈_ _∘_ Id
  dom : {A B : Obj} → Hom A B → Obj
  dom {A} _ = A
  cod : {A B : Obj} → Hom A B → Obj
  cod {B = B} _ = B

open Category

_[_≈_] : ∀ {c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {A B : Obj C} → Rel (Hom C A B) ℓ
C [ f ≈ g ] = Category._≈_ C f g
_[_∘_] : ∀ {c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f ∘ g ] = Category._∘_ C f g
