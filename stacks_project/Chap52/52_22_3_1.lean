/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Order.DepthDistance
import StacksCheckRecall

@[expose] public section

open scoped ENat

universe u v w x

/- 52.22.3.1 source-facing declarations.  The arithmetic hypotheses use
   addition in `WithBot ℕ∞`, so the source's integer differences are not
   represented by truncated subtraction at an underflow or bottom value. -/
/- The first source clause is unchanged; keep its explicit universe-level
   check so the facade continues to expose all source binders. -/
@[stacks 0EJL] #check
  (DepthDistance.depth_add_delta_eq :
    ∀ {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
      [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
      {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
      [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
      (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
      (δ' : ℕ∞) (fiberDim : WithBot ℕ∞),
      (WithBot.some (moduleDepth (Localization.AtPrime p')
          (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) =
        (WithBot.some (moduleDepth (Localization.AtPrime p)
          (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + fiberDim →
      (WithBot.some (moduleDepth (Localization.AtPrime p')
          (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) + (δ' : WithBot ℕ∞) =
        (WithBot.some (moduleDepth (Localization.AtPrime p)
            (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + fiberDim +
          (δ' : WithBot ℕ∞))
/- 52.22.3.1 (2): the lower-bound inequality in additive form, with the
   localized depth comparison and the source distance balance explicit. -/
@[stacks 0EJL] #check
  (DepthDistance.depth_delta_lower_bound :
    ∀ {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
      [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
      {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
      [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
      (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
      (δ δ' : ℕ∞) (fiberDim trdeg : WithBot ℕ∞) (d : ℕ),
      (WithBot.some (moduleDepth (Localization.AtPrime p')
          (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) =
        (WithBot.some (moduleDepth (Localization.AtPrime p)
          (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + fiberDim →
      (δ : WithBot ℕ∞) + trdeg ≤
        (δ' : WithBot ℕ∞) + ((d - 1 : ℕ) : WithBot ℕ∞) →
      (WithBot.some (moduleDepth (Localization.AtPrime p')
          (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) + (δ' : WithBot ℕ∞) +
          ((d - 1 : ℕ) : WithBot ℕ∞) ≥
        (WithBot.some (moduleDepth (Localization.AtPrime p)
            (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + (δ : WithBot ℕ∞) +
          fiberDim + trdeg)
/- 52.22.3.1 (3): the dimension balance in additive form, so it remains
   meaningful for the general `WithBot ℕ∞` dimension codomain. -/
@[stacks 0EJL] #check
  (DepthDistance.depth_delta_dimension_eq :
    ∀ {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
      [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
      {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
      [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
      (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
      (δ : ℕ∞) (fiberDim trdeg : WithBot ℕ∞),
      fiberDim + trdeg + ringKrullDim (R' ⧸ p') =
          ringKrullDim (R ⧸ p) →
      ((WithBot.some (moduleDepth (Localization.AtPrime p)
          (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + (δ : WithBot ℕ∞) +
          fiberDim + trdeg) + ringKrullDim (R' ⧸ p') =
        ((WithBot.some (moduleDepth (Localization.AtPrime p)
            (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + (δ : WithBot ℕ∞)) +
          ringKrullDim (R ⧸ p))
