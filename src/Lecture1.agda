{-# OPTIONS --safe --exact-split --without-K #-}
module Lecture1 where

open import Universes

O[_] : (f : ℕ → ℕ)
  → (g : ℕ → ℕ) → 𝒰₀ ᵖ
Ω[_] : (f : ℕ → ℕ)
  → (g : ℕ → ℕ) → 𝒰₀ ᵖ
o[_] : (f : ℕ → ℕ)
  → (g : ℕ → ℕ) → 𝒰₀ ᵖ
Θ[_] : (f : ℕ → ℕ)
  → (g : ℕ → ℕ) → 𝒰₀ ᵖ
