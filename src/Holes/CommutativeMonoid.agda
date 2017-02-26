
module Holes.CommutativeMonoid where

open import Algebra using (CommutativeMonoid)
open import Holes.Prelude
open import Holes.Util
open import Holes.Cong.Limited

module _ {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where

  open CommutativeMonoid commutativeMonoid

  open CongSplit _≈_ refl

  ∙-cong₁ = two→one₁ ∙-cong
  ∙-cong₂ = two→one₂ ∙-cong

database = (quote CommutativeMonoid._∙_ , 1 , quote ∙-cong₁)
         ∷ (quote CommutativeMonoid._∙_ , 2 , quote ∙-cong₂)
         ∷ []

open AutoCong database public
