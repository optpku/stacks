/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.IdealPowerTorsion.Action
public import ReasLib.Algebra.Module.Injective.MaximalIdeal
public import ReasLib.Algebra.Module.MatlisDuality.Completion

@[expose] public section

noncomputable section

universe u v

namespace Module.IsIdealPowerTorsion

/-- The canonical monoid homomorphism from completion units to automorphisms of an
ideal-power-torsion module. -/
def completionUnitsToAut
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hM : Module.IsIdealPowerTorsion I M) :
    (AdicCompletion I R)ˣ →* CategoryTheory.Aut (ModuleCat.of R M) :=
  (CategoryTheory.Aut.unitsEndEquivAut (ModuleCat.of R M)).toMonoidHom.comp
    (Units.map
      ((ModuleCat.endRingEquiv (ModuleCat.of R M)).symm.toRingHom.comp
        (Module.IsIdealPowerTorsion.completionToEnd I hM)).toMonoidHom)

end Module.IsIdealPowerTorsion

namespace LinearMap.IsInjectiveHull

/-- Completion units act bijectively on an injective hull of the residue field. -/
theorem completionUnitsToAut_bijective
    (A : Type u) (E : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull) :
    Function.Bijective
      (Module.IsIdealPowerTorsion.completionUnitsToAut
        (IsLocalRing.maximalIdeal A) (hι.maximalIdealPowerTorsion A E)) := sorry

end LinearMap.IsInjectiveHull
