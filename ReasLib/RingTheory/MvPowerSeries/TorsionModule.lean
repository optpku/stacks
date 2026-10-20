module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.RingTheory.MvPowerSeries.Derivation

@[expose] public section

universe u v w

namespace Module

/-- A maximal-ideal-power-torsion module over a positive-dimensional formal power-series
ring over a characteristic-zero field, endowed with additive operators satisfying the
coordinate Leibniz rules, is isomorphic to a direct sum of copies of an injective hull of
the residue field. -/
theorem equivDirectSumInjectiveHull_of_partialDerivations
    (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d)
    (M : Type v) (E : Type w)
    [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M]
    [AddCommGroup E] [Module (MvPowerSeries (Fin d) k) E]
    [Module.Injective (MvPowerSeries (Fin d) k) E]
    (ι : IsLocalRing.ResidueField (MvPowerSeries (Fin d) k) →ₗ[MvPowerSeries (Fin d) k]
      E)
    (hι : ι.IsInjectiveHull) (D : Fin d → M →+ M)
    (hD : ∀ (i : Fin d) (f : MvPowerSeries (Fin d) k) (z : M),
      D i (f • z) = MvPowerSeries.partialDeriv i f • z + f • D i z)
    (hM : IsIdealPowerTorsion
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)) M) :
    ∃ J : Type v,
      Nonempty (M ≃ₗ[MvPowerSeries (Fin d) k] DirectSum J (fun _ ↦ E)) := sorry

end Module
