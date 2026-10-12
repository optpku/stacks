/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.Localization

@[expose] public section

open scoped ENat

universe u v w x

namespace DepthDistance

/-- A localized depth-additivity equality remains valid after adding a target distance. -/
theorem depth_add_delta_eq
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
    {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
    (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
    (δ' : ℕ∞) (fiberDim : WithBot ℕ∞)
    (hDepth :
      (WithBot.some (moduleDepth (Localization.AtPrime p')
          (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) =
        (WithBot.some (moduleDepth (Localization.AtPrime p)
          (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + fiberDim) :
    (WithBot.some (moduleDepth (Localization.AtPrime p')
        (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) + (δ' : WithBot ℕ∞) =
      (WithBot.some (moduleDepth (Localization.AtPrime p)
          (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + fiberDim +
        (δ' : WithBot ℕ∞) := sorry

/-- A distance comparison yields the corresponding lower bound for localized depth. -/
theorem depth_delta_lower_bound
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
    {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
    (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
    (δ δ' : ℕ∞) (fiberDim trdeg : WithBot ℕ∞) (d : ℕ)
    (hDelta :
      (δ : WithBot ℕ∞) ≤
        WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
          ((δ' : WithBot ℕ∞) + trdeg) ((d - 1 : ℕ) : WithBot ℕ∞)) :
    (WithBot.some (moduleDepth (Localization.AtPrime p')
        (LocalizedModule.AtPrime p' M')) : WithBot ℕ∞) + (δ' : WithBot ℕ∞) ≥
      WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
        ((WithBot.some (moduleDepth (Localization.AtPrime p)
            (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + (δ : WithBot ℕ∞) +
          fiberDim + trdeg) ((d - 1 : ℕ) : WithBot ℕ∞) := sorry

/-- The fibre-dimension and residue-transcendence terms equal the quotient-dimension difference. -/
theorem depth_delta_dimension_eq
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R] [IsNoetherianRing R']
    {M : Type w} {M' : Type x} [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R' M'] [Module.Finite R M] [Module.Finite R' M']
    (p : Ideal R) (p' : Ideal R') [p.IsPrime] [p'.IsPrime]
    (δ : ℕ∞) (fiberDim trdeg : WithBot ℕ∞) (d : ℕ)
    (hDimension :
      fiberDim + trdeg =
        WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
          (ringKrullDim (R ⧸ p)) (ringKrullDim (R' ⧸ p'))) :
    WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
        ((WithBot.some (moduleDepth (Localization.AtPrime p)
            (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) + (δ : WithBot ℕ∞) +
          fiberDim + trdeg) ((d - 1 : ℕ) : WithBot ℕ∞) =
      WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
        ((WithBot.map₂ (fun a b : ℕ∞ ↦ a - b)
            ((WithBot.some (moduleDepth (Localization.AtPrime p)
                (LocalizedModule.AtPrime p M)) : WithBot ℕ∞) +
              (δ : WithBot ℕ∞)) ((d - 1 : ℕ) : WithBot ℕ∞)) +
          ringKrullDim (R ⧸ p)) (ringKrullDim (R' ⧸ p')) := sorry

end DepthDistance
