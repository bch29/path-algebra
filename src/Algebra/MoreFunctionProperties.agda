open import Level
open import Relation.Binary

module Algebra.MoreFunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.FunctionProperties _≈_

open import Data.Sum

sel⟶idp : (_∙_ : Op₂ A) → Selective _∙_ → Idempotent _∙_
sel⟶idp _∙_ selective x with selective x x
... | inj₁ x∙x≈x = x∙x≈x
... | inj₂ x∙x≈x = x∙x≈x
