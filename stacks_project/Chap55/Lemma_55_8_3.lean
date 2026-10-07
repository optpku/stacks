module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.SmoothCurveModel

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

/- Lemma 55.8.3 (1): a flat finite-type model of a smooth curve over the fraction field
of a discrete valuation ring admits a resolution of singularities. -/
@[stacks 0C2U] #check
  (AlgebraicGeometry.Scheme.Hom.existsResolution_of_smoothCurveModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (C : SchemeOverField K) [Curve C] [Smooth C.hom]
      {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [FiniteType p]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))))) ,
      ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
        IsModification g ∧ Scheme.Regular Y)

/- Lemma 55.8.3 (2): every resolution of a flat finite-type model of a smooth curve is again a
model of that curve via its composite structural morphism. -/
@[stacks 0C2U] #check
  (AlgebraicGeometry.Scheme.Hom.resolution_isModel_of_smoothCurveModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (C : SchemeOverField K) [Curve C] [Smooth C.hom]
      {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] [FiniteType p]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      {Y : Scheme.{u}} (g : Y ⟶ X) [IsModification g] [Scheme.Regular Y],
      ∃ resolutionFiberIso : C ≅ Over.mk
          (pullback.snd (g ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        Flat (g ≫ p) ∧ FiniteType (g ≫ p))
