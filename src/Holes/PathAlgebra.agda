
module Holes.PathAlgebra where

open import Algebra.Path.Structure using (PathAlgebra)
open import Holes.Prelude
open import Holes.Util
open import Holes.Cong.Limited

module _ {c ℓ} (pathAlgebra : PathAlgebra c ℓ) where

  open PathAlgebra pathAlgebra

  open CongSplit _≈_ refl

  +-cong₁ = two→one₁ +-cong
  +-cong₂ = two→one₂ +-cong
  *-cong₁ = two→one₁ *-cong
  *-cong₂ = two→one₂ *-cong

database = (quote PathAlgebra._+_ , 3 , quote +-cong₁)
         ∷ (quote PathAlgebra._+_ , 4 , quote +-cong₂)
         ∷ (quote PathAlgebra._*_ , 3 , quote *-cong₂)
         ∷ (quote PathAlgebra._*_ , 4 , quote *-cong₂)
         ∷ []

open AutoCong database public
