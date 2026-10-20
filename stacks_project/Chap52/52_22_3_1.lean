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

/- 52.22.3.1 (1): the depth-additivity equality after adding the target distance term. -/
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

/- 52.22.3.1 (2): the lower-bound inequality involving depth, distance,
the formal-fibre dimension, residue transcendence degree, and `d - 1`. -/
@[stacks 0EJL] #check
  (DepthDistance.depth_delta_lower_bound :
    ∀ {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
      [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
      {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
      [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
      (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
      (δ δ' : ℕ∞) (fiberDim trdeg : WithBot ℕ∞) (d : ℕ),
      (δ : WithBot ℕ∞) ≤
          WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
            ((δ' : WithBot ℕ∞) + trdeg) ((d - 1 : ℕ) : WithBot ℕ∞) →
      (WithBot.some (moduleDepth (Localization.AtPrime p')
          (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) + (δ' : WithBot ℕ∞) ≥
        WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
          ((WithBot.some (moduleDepth (Localization.AtPrime p)
              (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + (δ : WithBot ℕ∞) +
            fiberDim + trdeg) ((d - 1 : ℕ) : WithBot ℕ∞))

/- 52.22.3.1 (3): the final equality rewriting the fibre and transcendence
terms as the difference of the two quotient dimensions. -/
@[stacks 0EJL] #check
  (DepthDistance.depth_delta_dimension_eq :
    ∀ {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
      [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
      {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
      [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
      (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
      (δ : ℕ∞) (fiberDim trdeg : WithBot ℕ∞) (d : ℕ),
      fiberDim + trdeg =
          WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
            (ringKrullDim (R ⧸ p)) (ringKrullDim (R' ⧸ p')) →
      WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
          ((WithBot.some (moduleDepth (Localization.AtPrime p)
              (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + (δ : WithBot ℕ∞) +
            fiberDim + trdeg) ((d - 1 : ℕ) : WithBot ℕ∞) =
        WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
          ((WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
              ((WithBot.some (moduleDepth (Localization.AtPrime p)
                  (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) +
                (δ : WithBot ℕ∞)) ((d - 1 : ℕ) : WithBot ℕ∞)) +
            ringKrullDim (R ⧸ p)) (ringKrullDim (R' ⧸ p')))
