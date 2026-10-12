/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Directed
public import ReasLib.Algebra.Module.Injective.KernelAnnihilator
public import ReasLib.Algebra.Module.Injective.Torsion
public import ReasLib.RingTheory.LocalRing.Quotient

@[expose] public section

universe u v

namespace LinearMap.IsInjectiveHull

/-- For a Noetherian local ring, an injective hull of the residue field is
exhausted by the submodules annihilated by positive powers of the maximal ideal. -/
theorem maximalIdealPowerAnnihilatedStagesSup_eq_top
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (iota : IsLocalRing.ResidueField R →ₗ[R] E) (hiota : iota.IsInjectiveHull) :
    (IsLocalRing.maximalIdeal R).powerAnnihilatedStagesSup E = ⊤ := sorry

/-- For every positive exponent, the kernel annihilator of the corresponding
maximal-ideal-power quotient carries the induced injective hull of its residue
field. -/
theorem maximalIdealPowKernelAnnihilator
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (iota : IsLocalRing.ResidueField R →ₗ[R] E) (hiota : iota.IsInjectiveHull)
    (n : ℕ+) :
    (iota.toKernelAnnihilator
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n : ℕ)))
      Ideal.Quotient.mk_surjective).IsInjectiveHull := sorry

/-- For a Noetherian local ring, an injective hull of the residue field is
ideal-power torsion for the maximal ideal. -/
theorem maximalIdealPowerTorsion
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull) :
    Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal R) E := sorry

end LinearMap.IsInjectiveHull
