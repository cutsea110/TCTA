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

-- List is category
infixr 40 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixl 30 _++_
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
x ∷ xs ++ ys = x ∷ (xs ++ ys)
data ListObj : Set where
  ∗ : ListObj

open import Relation.Binary.PropositionalEquality
≡-cong = Relation.Binary.PropositionalEquality.cong

isListCategory : (A : Set) → IsCategory ListObj (λ a b → List A) _≡_ _++_ []
isListCategory A = record
                     { isEquivalence = isEquivalence1 {A}
                     ; identityL = list-id-l
                     ; identityR = list-id-r
                     ; ∘-resp-≈ =  ∘-resp-≈ {A}
                     ; associative = λ {a} {b} {c} {d} {x} {y} {z} → list-assoc {A} {x} {y} {z}
                     }
  where
    isEquivalence1 : {A : Set} → IsEquivalence {_} {_} {List A} _≡_
    isEquivalence1 {A} = record { refl = refl ; sym = sym ; trans = trans }
    list-id-l : {A : Set} {ys : List A} → [] ++ ys ≡ ys
    list-id-l {_} {_} = refl
    list-id-r : {A : Set} {xs : List A} → xs ++ [] ≡ xs
    list-id-r {_} {[]} = refl
    list-id-r {_} {x ∷ xs} = ≡-cong (λ y → x ∷ y) list-id-r
    ∘-resp-≈ : {A : Set} {f g : List A} {h i : List A} → f ≡ g → h ≡ i → h ++ f ≡ i ++ g
    ∘-resp-≈ {A} refl refl = refl
    list-assoc : {A : Set} {x y z : List A} → x ++ (y ++ z) ≡ (x ++ y) ++ z
    list-assoc {A} {[]} {ys} {zs} = refl
    list-assoc {A} {x ∷ xs} {ys} {zs} = ≡-cong (λ y →  x ∷ y) (list-assoc {A} {xs} {ys} {zs})

ListCategory : (A : Set) → Category _ _ _
ListCategory A = record
                   { Obj = ListObj
                   ; Hom = λ a b → List A
                   ; _∘_ = _++_
                   ; _≈_ = _≡_
                   ; Id = []
                   ; isCategory = isListCategory A
                   }
