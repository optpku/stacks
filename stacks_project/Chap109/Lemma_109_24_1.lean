module

public import stacks_project.Chap55.Definition_55_14_6
public import stacks_project.Chap109.Definition_109_22_2_Family

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Lemma 109.24.1: a smooth projective curve `C` over the fraction field `K` of a
discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K` and genus at least two, has
semistable reduction in the sense of Definition 55.14.6 if and only if there
exists a stable family of curves over `R` whose generic fibre is `C`. -/
@[stacks 0E8D]
theorem hasSemistableReduction_iff_existsStableFamily
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 2 ≤ SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections) :
    hasSemistableReduction R K C ↔
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
        (genericFiberIso : C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
        IsProper f ∧ IsStableFamily f := sorry

end AlgebraicGeometry.Scheme.Hom
