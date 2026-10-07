module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat finite-type model of a smooth curve over the fraction field of a discrete valuation
ring admits a regular modification. -/
theorem existsResolution_of_smoothCurveModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [FiniteType p]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), IsModification g ∧ Scheme.Regular Y := sorry

/-- Every regular modification of a flat finite-type model of a smooth curve is again a model of
the curve via its composite structural morphism. -/
theorem resolution_isModel_of_smoothCurveModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [FiniteType p]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    {Y : Scheme.{u}} (g : Y ⟶ X) [IsModification g] [Scheme.Regular Y] :
    ∃ resolutionFiberIso : C ≅ Over.mk
        (pullback.snd (g ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      Flat (g ≫ p) ∧ FiniteType (g ≫ p) := sorry

end AlgebraicGeometry.Scheme.Hom
