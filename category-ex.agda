module category-ex where

open import Level
open import Relation.Binary.Core

open import Category

postulate c₁ c₂ ℓ : Level
postulate A : Category c₁ c₂ ℓ

open Category.Category

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

open import Algebra.Structures
open import Algebra.FunctionProperties using (Op₁; Op₂)
data MonoidObj (c : Level) : Set c where
  ¡ : MonoidObj c

record ≡-Monoid c : Set (suc c) where
  infixl 7 _⋆_
  field
    Carrier : Set c
    _⋆_     : Op₂ Carrier
    ε       : Carrier
    isMonoid : IsMonoid _≡_ _⋆_ ε
open ≡-Monoid
open import Data.Product
isMonoidCategory : {c : Level} (M : ≡-Monoid c) → IsCategory (MonoidObj c) (λ a b → Carrier M) _≡_ (_⋆_ M) (ε M)
isMonoidCategory M = record
                       { isEquivalence = isEquivalence1 {_} {M}
                       ; identityL = λ {_} {_} {x} → (proj₁ (IsMonoid.identity (isMonoid M))) x
                       ; identityR = λ {_} {_} {x} → (proj₂ (IsMonoid.identity (isMonoid M))) x
                       ; ∘-resp-≈ = ∘-resp-≈ {_} {M}
                       ; associative = λ {a} {b} {c} {d} {x} {y} {z} → sym (IsMonoid.assoc (isMonoid M) x y z)
                       }
                 where
                   isEquivalence1 : ∀ {c}{M : ≡-Monoid c} → IsEquivalence {_} {_} {Carrier M} _≡_
                   isEquivalence1 {A} = record { refl = refl ; sym = sym ; trans = trans }
                   ∘-resp-≈ : ∀ {c}{M : ≡-Monoid c} {f g : Carrier M} {h i : Carrier M} →
                              f ≡ g → h ≡ i → (M ⋆ h) f ≡ (M ⋆ i) g
                   ∘-resp-≈ {A} refl refl = refl

MonoidCategory : ∀{c} (M : ≡-Monoid c) → Category _ _ _
MonoidCategory {c} M = record
                       { Obj = MonoidObj c
                       ; Hom = λ a b → Carrier M 
                       ; _∘_ = _⋆_ M
                       ; _≈_ = _≡_
                       ; Id = ε M
                       ; isCategory = isMonoidCategory M
                       }

