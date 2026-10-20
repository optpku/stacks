module

public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Model
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.AtWorstNodal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth projective curve over the fraction field of a discrete valuation ring,
with only constant global functions, has semistable reduction if and only if it admits
a proper flat finite-type at-worst-nodal model with the specified generic fibre. -/
theorem hasSemistableReduction_iff_existsAtWorstNodalModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    hasSemistableReduction R K C ↔
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
        (genericFiberIso : C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
        Flat f ∧ FiniteType f ∧ IsProper f ∧ AtWorstNodal f := sorry

end AlgebraicGeometry.Scheme.Hom
