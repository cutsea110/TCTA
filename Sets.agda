module Sets where

open import Category
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
open import Level

_∘_ : ∀ {ℓ} {A B C : Set ℓ} → (f : B → C) → (g : A → B) → A → C
_∘_ f g x = f (g x)
_-Set⟶_ : ∀ {ℓ} → (A B : Set ℓ) → Set _
A -Set⟶ B = A → B
SetId : ∀ {ℓ} {A : Set ℓ} → A → A
SetId x = x
Sets : ∀ {ℓ} → Category _ _ ℓ
Sets {ℓ} = record
             { Obj = Set ℓ
             ; Hom = _-Set⟶_
             ; _∘_ = _∘_
             ; _≈_ = _≡_
             ; Id = SetId
             ; isCategory = isCategory
             }
     where
       isCategory : IsCategory (Set ℓ) _-Set⟶_ _≡_ _∘_ SetId
       isCategory = record
                      { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
                      ; identityL = refl
                      ; identityR = refl
                      ; ∘-resp-≈ = ∘-resp-≈
                      ; associative = refl
                      }
                  where
                    ∘-resp-≈ : {A B C : Set ℓ} {f g : A -Set⟶ B} {h i : B -Set⟶ C} → f ≡ g → h ≡ i → h ∘ f ≡ i ∘ g
                    ∘-resp-≈ refl refl = refl
