module category-ex where

open import Level
open import Cat
postulate c₁ c₂ ℓ : Level
postulate A : Category c₁ c₂ ℓ

obj : Set c₁
obj = Cat.Category.Obj A
hom : Category.Obj A → Category.Obj A → Set c₂
hom = Cat.Category.Hom A
x : {A = A₁ : Category.Obj A} {B : Category.Obj A} → Category.Hom A A₁ B → Category.Obj A
x = Cat.Category.dom A
y : {A = A₁ : Category.Obj A} {B : Category.Obj A} → Category.Hom A A₁ B → Category.Obj A
y = Cat.Category.cod A
