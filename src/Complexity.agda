{-# OPTIONS --safe --exact-split --prop #-}
module Complexity where

open import PropUniverses

open import TuringMachine hiding (⊔)

module WithSymbols (𝕊 : Symbols 𝒰) where
  private instance _ = 𝕊

  open import Type.Subset
  open import Proposition.Identity
  open import Data.Nat hiding (_⊔_)
  open import Data.ExtendedNat
  open import Data.Collection
  open import Logic

  open import BigO-Notation

  -- TODO: ask for definition of "running time" (whether on reject too?)
  running-time : (M : TuringMachine 𝕊 𝒱) → ℕ → ℕ∞
  running-time M m = ? -- maximum (fmap (len ∘ get-computation M) $ all inputs) 

  _in-TIME[_[n]] :
    (L : subset 𝒱 (Σ *))
    (f : ℕ → ℕ)
    →
    𝒰 ⁺ ⊔ 𝒱 ⁺ ᵖ
  _in-TIME[_[n]] {𝒱} L f =
    ∃ λ (M : TuringMachine 𝕊 𝒱) →
    (∀ (x : Σ *) → x ∈ accepted-language M ↔ x ∈ L) ∧
    running-time M is-O[ f [n]] 
    
