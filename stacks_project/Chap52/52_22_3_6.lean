/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Depth.DimensionDelta

open scoped ENat

universe u v w x

/- 52.22.3.6: for completed local rings `R`, `R'`, completed stalk modules `M`, `M'`,
and primes `p`, `p'`, the comparison from 52.22.3.1, with the quotient-dimension difference
added before truncated subtraction, implies the stated lower bound involving `δ`, `δ'`, and `d`. -/
@[stacks 0EJM] #check (Module.depth_add_quotientDim_delta_ge :
  ∀
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
          ((d - 1 : ℕ) : WithBot ℕ∞)),
    (WithBot.some (moduleDepth (Localization.AtPrime p') (LocalizedModule.AtPrime p' M')) :
        WithBot ℕ∞) + ringKrullDim (R' ⧸ p') + (δ' : WithBot ℕ∞) ≥
      WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
        ((WithBot.some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :
            WithBot ℕ∞) + ringKrullDim (R ⧸ p) + (δ : WithBot ℕ∞))
        ((d - 1 : ℕ) : WithBot ℕ∞))
