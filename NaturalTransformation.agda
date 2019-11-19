module NaturalTransformation where

open import Level
open import Category
open import Functor

open Category.Category
open Functor.Functor

record IsNTrans {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (D : Category c₁ c₂ ℓ) (C : Category c₁′ c₂′ ℓ′)
                (F G : Functor D C)
                (TMap : (A : Obj D) → Hom C (FObj F A) (FObj G A))
                : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
       field
         commute : {a b : Obj D} {f : Hom D a b} → C [ C [ FMap G f ∘ TMap a ] ≈ C [ TMap b ∘ FMap F f ] ]
