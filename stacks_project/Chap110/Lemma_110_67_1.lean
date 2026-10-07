module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_47_3_RationalFunction
public import stacks_project.Chap99.Lemma_99_13_1_Spaces

/-!
# A family of curves whose total space is not a scheme
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 110.67.1: there exists a field `k` and a family of curves
`X ⟶ affineLine (Spec (CommRingCat.of k))` such that `X` is not a scheme. -/
@[stacks 0D5E]
theorem exists_familyOfCurves_affineLine_not_isScheme :
    ∃ (k : Type u) (_ : Field k)
      (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      (f : X ⟶ affineLine (Spec (CommRingCat.of k))),
      FpFlatProper f ∧ RelativeDimensionLE f 1 ∧ ¬ IsScheme X :=
  sorry

/-- There exists a field `k` and a proper, flat, finitely presented morphism
`f : X ⟶ affineLine (Spec (CommRingCat.of k))` of relative dimension at most `1`
whose source is not a scheme. -/
theorem exists_familyOfCurves_affineLine_not_isScheme_spec :
    ∃ (k : Type u) (_ : Field k)
      (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      (f : X ⟶ affineLine (Spec (CommRingCat.of k))),
      FinitePresentation f ∧ Flat f ∧ Proper f ∧
        RelativeDimensionLE f 1 ∧ ¬ IsScheme X :=
  sorry

/-- A family of curves over the affine line of a field need not have total space
a scheme. -/
theorem not_forall_familyOfCurves_affineLine_isScheme :
    ¬ ∀ (k : Type u) [Field k]
        (X : AlgebraicSpace (Spec (CommRingCat.of k)))
        (f : X ⟶ affineLine (Spec (CommRingCat.of k))),
        FpFlatProper f → RelativeDimensionLE f 1 → IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
