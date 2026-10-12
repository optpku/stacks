/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_37_5_Reduction

/-!
# Reduction of recompletion along a closed subset

The reduction of the completion of a formal algebraic space along a closed
subset of its reduction is the reduced induced closed subspace on that subset.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points ClosedSubspaceStructure)
open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.37.5: Let `S` be a scheme. Let `X` be a formal algebraic space over
`S`. Let `T ⊆ Points (reduction X)` be a closed subset. The reduction of the
completion `completionAlong X T` is the reduced induced closed subspace of
`reduction X` corresponding to `T`. -/
@[stacks 0GVU]
theorem reduction_completionAlong {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) :
    reduction (completionAlong X T) =
      (ClosedSubspaceStructure.reduced T).space :=
  sorry

/-- The structure morphism of the reduction of `completionAlong X T` is the
canonical map `fromReduced T` from the reduced induced closed subspace. -/
theorem reductionι_completionAlong {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) :
    reductionι (completionAlong X T) = completionAlong.fromReduced T :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
