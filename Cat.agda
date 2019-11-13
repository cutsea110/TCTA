module Cat where

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
         ∘-resp-≈ : {A B C : Obj} → {f g : Hom A B}{h i : Hom B C} → f ≈ g → h ≈ i → (h ∘ f) ≈ (i ∘ g)
         associative : {A B C D : Obj}{f : Hom C D}{g : Hom B C}{h : Hom A B} → (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)
