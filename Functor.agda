module Functor where

open import Level
open import Relation.Binary.Core
open import Category

open Category.Category

_[_≈_] : ∀ {c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {A B : Obj C} → Rel (Hom C A B) ℓ
C [ f ≈ g ] = Category._≈_ C f g
_[_∘_] : ∀ {c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f ∘ g ] = Category._∘_ C f g

record IsFunctor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁′ c₂′ ℓ′)
                 (FObj : Obj C → Obj D)
                 (FMap : {A B : Obj C} → Hom C A B → Hom D (FObj A) (FObj B))
                 : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
       field
         ≈-cong : {A B : Obj C} {f g : Hom C A B} → C [ f ≈ g ] → D [ FMap f ≈ FMap g ]
         identity : {A : Obj C} →  D [ (FMap {A} {A} (Id C {A})) ≈ Id D {FObj A} ]
         distr : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c} → D [ FMap (C [ g ∘ f ]) ≈ (D [ FMap g ∘ FMap f ]) ]

record Functor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (domain : Category c₁ c₂ ℓ) (codomain : Category c₁′ c₂′ ℓ′)
  : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    FObj : Obj domain → Obj codomain
    FMap : {A B : Obj domain} → Hom domain A B → Hom codomain (FObj A) (FObj B)
    isFunctor : IsFunctor domain codomain FObj FMap

open Functor
-- distributive law
-- T(g f) ≡ T(g) T(f)
Lemma1 : {c₁ c₂ ℓ : Level} {A : Category c₁ c₂ ℓ} (T : Functor A A) → {a b c : Obj A} {g : Hom A b c} {f : Hom A a b}
         → A [ (FMap T (A [ g ∘ f ])) ≈ (A [ FMap T g ∘ FMap T f ]) ]
Lemma1 t = IsFunctor.distr (isFunctor t)
