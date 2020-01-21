{-# OPTIONS --safe --exact-split --prop #-}
module BigO-Notation where

open import PropUniverses
open import Data.Nat
open import Logic

_is-O[_[n]] : (g f : ℕ → ℕ) → 𝒰₀ ᵖ
g is-O[ f [n]] = ∃ λ k → 0 < k ∧ ∃ λ m → ∀ n (p : m < n) → g n ≤ k * f n 
_is-Ω[_[n]] : (g f : ℕ → ℕ) → 𝒰₀ ᵖ
g is-Ω[ f [n]] = ∃ λ k → 0 < k ∧ ∃ λ m → ∀ n (p : m < n) → k * f n ≤ g n
_is-Θ[_[n]] : (g f : ℕ → ℕ) → 𝒰₀ ᵖ
g is-Θ[ f [n]] =
  ∃ λ k₀ → 0 < k₀ ∧
  ∃ λ k₁ → 0 < k₁ ∧
  ∃ λ m → ∀ n (p : m < n) →
    k₀ * f n ≤ g n ∧ g n ≤ k₁ * f n
