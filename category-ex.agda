module category-ex where

open import Level
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

postulate a b : Obj A
postulate f g : Hom A a b
