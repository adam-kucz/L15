{-# OPTIONS --safe --exact-split --prop #-}
module TuringMachine.Property where

open import TuringMachine.Definition as TM
  using (Symbols; TuringMachine)

open import Universes

module WithTuringMachine
    {𝕊 : Symbols 𝒰}
    (M : TuringMachine 𝕊 𝒱)
    where
  open TM.WithTuringMachine M
  
  open import Logic

  deterministic-and-well-defined :
    ∀ (conf₀ : Configuration) →
    ∃! λ (conf₁ : Configuration) →
    conf₀ ⟶ conf₁
  deterministic-and-well-defined = {!_⟶_!}
