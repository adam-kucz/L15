{-# OPTIONS --safe --exact-split --prop #-}
module DecisionProblem where

open import PropUniverses
open import Data.List
private
  _* = List

open import Type.Finite
open import Type.Subset
open import Proposition.Sum

DecisionProblem : (Σ : Finite 𝒰) → 𝒰 ⁺ ˙
DecisionProblem {𝒰} (Σ , _) = subset 𝒰 (Σ *)

open import MachineModel

_is-decidable-by_ :
  {Σ : Finite 𝒰}
  (dp : DecisionProblem Σ)
  (M : MachineModel 𝒱 𝒲 𝒯 Σ)
  → 𝒰 ⊔ 𝒱 ⊔ 𝒲 ᵖ
dp is-decidable-by M =
  ∃ λ (f : Algorithm) →
  ∀ x → (decision-yes f x → x ∈ dp) ∧ (decision-no f x → x ∉ dp)
  where instance _ = M
  
open import Proposition.Identity

_can-compute_ :
  {Σ : Finite 𝒰}
  (M : MachineModel 𝒱 𝒲 𝒯 Σ)
  → let instance _ = M in
  (f : elem Σ * → Δ *)
  → 𝒰 ⊔ 𝒱 ⊔ 𝒯 ᵖ
M can-compute f =
  ∃ λ (alg : Algorithm) →
  ∀ x → output alg x == f x
  where instance _ = M

is-computable-by-syntax = _can-compute_
syntax is-computable-by-syntax M f = f is-comutable-by M
