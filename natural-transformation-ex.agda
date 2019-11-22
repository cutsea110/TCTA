module natural-transformation-ex where

open import Relation.Binary
open import NaturalTransformation

open NaturalTransformation.IsNTrans

open import Level
open import Category
open import Functor

postulate c₁ c₂ ℓ : Level
postulate A : Category c₁ c₂ ℓ

identityFunctor : Functor A A
identityFunctor = record { FObj = λ x → x
                         ; FMap = λ x → x
                         ; isFunctor = isFunctor
                         }
                where
                  isFunctor : ∀{ c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → IsFunctor C C (λ x → x) (λ x → x)
                  isFunctor {C = C} = record { ≈-cong = λ x → x
                                             ; identity = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C))
                                             ; distr = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C))
                                             }

postulate T : Functor A A
postulate η : NTrans A A identityFunctor T
