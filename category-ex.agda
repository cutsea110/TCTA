module category-ex where

open import Level
open import Relation.Binary.Core

open import Cat
postulate c₁ c₂ ℓ : Level
postulate A : Category c₁ c₂ ℓ

open Cat.Category

obj : Set c₁
obj = Obj A
hom : Obj A → Obj A → Set c₂
hom = Hom A
x : {A = A₁ : Obj A} {B : Obj A} → Hom A A₁ B → Obj A
x = dom A
y : {A = A₁ : Obj A} {B : Obj A} → Hom A A₁ B → Obj A
y = cod A

postulate a b c : Obj A
postulate g : Hom A a b
postulate f : Hom A b c

h = _∘_ A f g

_[_≈_] : ∀ {c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {A B : Obj C} → Rel (Hom C A B) ℓ
C [ f ≈ g ] = Category._≈_ C f g
_[_∘_] : ∀ {c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f ∘ g ] = Category._∘_ C f g

i : Hom A a c
i = A [ f ∘ g ]

