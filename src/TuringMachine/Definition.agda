{-# OPTIONS --safe --exact-split --prop #-}
module TuringMachine.Definition where

open import PropUniverses renaming (_⊔_ to _⨿_)
open import Proposition.Sum hiding (_,_)
open import Type.Sum hiding (Σ)
open import Type.BinarySum
open import Type.Finite

module Syntax where
  data Final : 𝒰₀ ˙ where
    acc rej : Final

  data Move : 𝒰₀ ˙ where
    L R S : Move

open Syntax
open import Proposition.Identity

record Symbols 𝒰 : 𝒰 ⁺ ˙ where
  field
    Σ' : Finite 𝒰
  Σ = elem Σ'
  field
    ⊔ ▷ : Σ
    ⊔≠▷ : ⊔ ≠ ▷

open Symbols ⦃ … ⦄ public

record TuringMachine (𝕊 : Symbols 𝒰) 𝒱 : 𝒰 ⁺ ⨿ 𝒱 ⁺ ˙ where
  private instance _ = 𝕊
  field
    K' : Finite 𝒱
  K = elem K'
  field
    s : K
    δ : K × Σ → (K + Final) × Σ × Move

open TuringMachine ⦃ … ⦄ public

open import Data.List
infixl 58 _*
_* = List
  
module WithTuringMachine
    {𝕊 : Symbols 𝒰}
    (M : TuringMachine 𝕊 𝒱)
    where
  private instance _ = M; _ = 𝕊

  Configuration : 𝒰 ⨿ 𝒱 ˙
  Configuration = (K + Final) × Σ * × Σ *
  
  open import Relation.Binary
  open import Data.Collection

  infixl 35 _⟶_
  data _⟶_ : Rel (𝒰 ⨿ 𝒱) Configuration Configuration where
    L-step :
      ∀ {q v a u} → let (q' , b , D) = δ ⦃ M ⦄ (q , a) in
      (p : D == L)
      → --------------------------------------------------------------------
      (inl q , v ++ [ a ] , u) ⟶ (q' , v , b ∷ u)
  
    S-step :
      ∀ {q v a u}
      → let (q' , b , D) = δ ⦃ M ⦄ (q , a) in
      (p : D == S)
      → --------------------------------------------------------------------
      (inl q , v ++ [ a ] , u) ⟶ (q' , v ++ [ b ] , u)
  
    R-step-mid :
      ∀ {q v a c x}
      → let (q' , b , D) = δ ⦃ M ⦄ (q , a) in
      (p : D == R)
      → --------------------------------------------------------------------
      (inl q , v ++ [ a ] , c ∷ x) ⟶ (q' , v ++ [ b ⸴ c ] , x)
  
    R-step-edge :
      ∀ {q v a}
      → let (q' , b , D) = δ ⦃ M ⦄ (q , a)
            instance _ = M in
      (p : D == R)
      → --------------------------------------------------------------------
      (inl q , v ++ [ a ] , []) ⟶ (q' , v ++ [ b ⸴ ⊔ ] , [])

  infix 35 _⟶*_
  _⟶*_ : Rel (𝒰 ⨿ 𝒱) Configuration Configuration
  _⟶*_ = refl-trans-close _⟶_
  
  open import Data.Nat
  open import Function.Proof
  
  Computation : 𝒰 ⨿ 𝒱 ˙
  Computation =
    Σₚ λ (lc : List Configuration) →
    ∀ i (p : i +1 < len lc) →
      lc ! i [ trans (postfix suc i) p ] ⟶ lc ! i +1 [ p ]
  
  open import Type.Subset
  
  accepted-language : subset (𝒰 ⨿ 𝒱) (Σ *)
  accepted-language x = ∃ λ w → ∃ λ u →
    (inl s , [ ▷ ] , x) ⟶* (inr acc , w , u)

  open import Logic hiding (_,_)

  halts-on : (x : Σ *) → 𝒰 ⨿ 𝒱 ᵖ
  halts-on x =  ∃ λ w → ∃ λ u →
    (inl s , [ ▷ ] , x) ⟶* (inr acc , w , u) ∨
    (inl s , [ ▷ ] , x) ⟶* (inr rej , w , u)

open WithTuringMachine public
