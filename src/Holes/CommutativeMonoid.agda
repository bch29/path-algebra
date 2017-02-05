open import Algebra using (CommutativeMonoid)

module Holes.CommutativeMonoid {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where

  open import Holes.Prelude
  open import Holes.Util
  open import Holes.Cong.Limited

  open CommutativeMonoid commutativeMonoid renaming (Carrier to A)

  open CongSplit _≈_ refl

  ∙-cong₁ = two→one₁ ∙-cong
  ∙-cong₂ = two→one₂ ∙-cong

  database = (quote _∙_ , 0 , quote-term ∙-cong₁)
           ∷ (quote _∙_ , 1 , quote-term ∙-cong₂)
           ∷ []

  open AutoCong database public
