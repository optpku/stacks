/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.SpecialFiber
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper regular model of a smooth projective curve is minimal exactly when its associated
numerical type is minimal. -/
theorem isMinimalModel_iff_associatedNumericalType_isMinimal
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (hT : T.IsSpecialFiberType R K f
      (regularModel_genericFiberProperties R K C h_globalSections f genericFiberIso)) :
    IsMinimalModel f ↔ T.IsMinimal := sorry

end AlgebraicGeometry.Scheme.Hom
