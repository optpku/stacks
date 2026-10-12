/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_9_14_Union

/-!
# Union of open substacks

A family of open substacks of an algebraic stack has a union open substack
which they cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

open OpenSubstack

/-- Lemma 100.9.14 (1): Let `X` be an algebraic stack and `U i ⊂ X` a collection
of open substacks indexed by `i : I`. Then each `U i` is an open substack of
`iUnion U ⊂ X`, via the factorization `iUnionι U i ≫ (iUnion U).ι = (U i).ι`. -/
@[stacks 05UQ]
theorem iUnionι_isOpenSubstack {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {I : Type v} (U : I → OpenSubstack X) (i : I) :
    iUnionι U i ≫ (iUnion U).ι = (U i).ι := sorry

/-- Lemma 100.9.14 (2): Let `X` be an algebraic stack and `U i ⊂ X` a collection
of open substacks indexed by `i : I`. Then the open substacks `U i` cover
`iUnion U`. -/
@[stacks 05UQ]
theorem iUnion_cover {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {I : Type v} (U : I → OpenSubstack X) (x : Points (iUnion U).Y) :
    ∃ i, x ∈ Set.range (Points.map (iUnionι U i)) := sorry

end AlgebraicGeometry.AlgebraicStack
