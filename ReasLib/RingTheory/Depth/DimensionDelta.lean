/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.KrullDimension.Module

@[expose] public section

open scoped ENat

universe u v w x

namespace Module

/-- For finite modules over Noetherian local rings, a comparison of localized depths plus
delta values, after adding the difference of quotient dimensions before truncated subtraction,
implies the corresponding comparison of depth plus quotient dimension plus delta, with correction
`d - 1`. -/
theorem depth_add_quotientDim_delta_ge
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
    {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
    (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime] (δ δ' : ℕ∞) (d : ℕ)
    (h_dimension : ringKrullDim (R' ⧸ p') ≤ ringKrullDim (R ⧸ p))
    (h_depth_delta :
      (WithBot.some (moduleDepth (Localization.AtPrime p') (LocalizedModule.AtPrime p' M')) :
          WithBot ℕ∞) + (δ' : WithBot ℕ∞) ≥
        WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
          ((WithBot.some
                (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :
              WithBot ℕ∞) + (δ : WithBot ℕ∞) +
            WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
              (ringKrullDim (R ⧸ p)) (ringKrullDim (R' ⧸ p')))
          ((d - 1 : ℕ) : WithBot ℕ∞)) :
    (WithBot.some (moduleDepth (Localization.AtPrime p') (LocalizedModule.AtPrime p' M')) :
        WithBot ℕ∞) + ringKrullDim (R' ⧸ p') + (δ' : WithBot ℕ∞) ≥
      WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
        ((WithBot.some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :
            WithBot ℕ∞) + ringKrullDim (R ⧸ p) + (δ : WithBot ℕ∞))
        ((d - 1 : ℕ) : WithBot ℕ∞) := sorry

end Module
