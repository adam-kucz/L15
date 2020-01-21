{-# OPTIONS --safe --exact-split --prop #-}
module MachineModel where

open import PropUniverses
open import Data.List
private
  _* = List

open import Proposition.Sum
open import Type.Finite

record MachineModel 𝒰 𝒱 𝒲 (X : Finite 𝒯) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ⊔ 𝒲 ⁺ ⊔ 𝒯 ˙ where
  private
    Σ = elem  X
  field
    Algorithm : 𝒰 ˙
    decision-yes : (a : Algorithm)(x : Σ *) → 𝒱 ᵖ
    decision-no : (a : Algorithm)(x : Σ *) → 𝒱 ᵖ
    Δ : 𝒲 ˙
    output : (a : Algorithm)(x : Σ *) → Δ *

open MachineModel ⦃ … ⦄ public
