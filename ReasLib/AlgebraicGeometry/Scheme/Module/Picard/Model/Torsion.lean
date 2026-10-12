/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Thickening.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.Numerical
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.TrivialPower
public import ReasLib.Algebra.Group.Torsion.Map
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AddSubgroup
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a regular proper flat model over a discrete valuation ring of a smooth
proper curve with only constant global sections, pullback to the reduced special
fibre is injective on the `h`-torsion Picard subgroup when `h` is a unit in the
residue field. -/
theorem picardPullback_specialFiberReduction_injective
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (h : ℤ)
    (h_unit : IsUnit (h : IsLocalRing.ResidueField R)) :
    Set.InjOn
      (Scheme.Hom.picardPullback
        (Scheme.reductionι (f.fiber (IsLocalRing.closedPoint R)) ≫
          f.fiberι (IsLocalRing.closedPoint R)))
      X.PicardGroup[h] := sorry

/-- For a regular proper flat model of a smooth projective curve, generic-fibre
restriction and the canonical numerical Picard map are exact on `h`-torsion
when `h` is positive and coprime to the special-fibre multiplicity gcd. -/
theorem picardTorsionSequence_exact
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components)
    (h : ℤ) (h_pos : (1 : ℤ) ≤ h)
    (h_coprime : IsCoprime h (specialFiberMultiplicityGcd f T.n components : ℤ)) :
    Function.Injective ((genericFiberPicardRestriction f genericFiberIso).torsionByMap h) ∧
      Function.Exact
        ((genericFiberPicardRestriction f genericFiberIso).torsionByMap h)
        ((picardToNumerical π hπ C h_globalSections f genericFiberIso T components hT).torsionByMap h) := sorry

end AlgebraicGeometry.Scheme.Hom
