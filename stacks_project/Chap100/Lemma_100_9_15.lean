/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_9_14_Union
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact

/-!
# Finite subcover of a quasi-compact open substack

A quasi-compact open substack contained in a union of open substacks is
already contained in the union of a finite subfamily.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack.OpenSubstack

/-- Lemma 100.9.15: Let `X` be an algebraic stack and `X'` a quasi-compact
open substack of `X`. If `U` is a family of open substacks of `X` with
`X'.objectProperty ≤ (iUnion U).objectProperty`, using the union of Lemma
100.9.14, then there exists a finite subset `t : Finset I` such that
`X'.objectProperty ≤ (iUnion (fun i : t ↦ U i)).objectProperty`. -/
@[stacks 05UR]
theorem exists_finset_iUnion {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (X' : OpenSubstack X) [IsQuasiCompact X'.Y]
    {I : Type v} (U : I → OpenSubstack X)
    (h : X'.objectProperty ≤ (iUnion U).objectProperty) :
    ∃ t : Finset I,
      X'.objectProperty ≤ (iUnion (fun i : t ↦ U i)).objectProperty :=
  sorry

/-- If the inclusion of a quasi-compact open substack `X'` factors through
`iUnion U`, then it factors through the union of some finite subfamily. -/
theorem exists_finset_iUnion_of_factors {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (X' : OpenSubstack X) [IsQuasiCompact X'.Y]
    {I : Type v} (U : I → OpenSubstack X)
    (h : ∃ f : X'.Y ⟶ (iUnion U).Y, f ≫ (iUnion U).ι = X'.ι) :
    ∃ t : Finset I, ∃ g : X'.Y ⟶ (iUnion (fun i : t ↦ U i)).Y,
      g ≫ (iUnion (fun i : t ↦ U i)).ι = X'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicStack.OpenSubstack
