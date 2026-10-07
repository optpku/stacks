module

public import stacks_project.Chap87.Lemma_87_14_5_Reduction

/-!
# Reduction of the completion along a closed subset

The reduction of the formal completion of an algebraic space along a closed
subset is the reduced induced closed subspace corresponding to that subset.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 87.14.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `T ⊆ Points X` be a closed subset. The reduction of the completion
`completionAlong X T` of `X` along `T` is the reduced induced closed subspace
of `X` corresponding to `T`. -/
@[stacks 0GB9]
theorem reduction_completionAlong {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.reduction (completionAlong X T) =
      (ClosedSubspaceStructure.reduced T).space :=
  sorry

/-- The structure morphism of the reduction of `completionAlong X T` is the
canonical map `fromReduced T` from the reduced induced closed subspace. -/
theorem reductionι_completionAlong {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.reductionι (completionAlong X T) =
      completionAlong.fromReduced T :=
  sorry

/-- A morphism `g : Y ⟶ X` from a reduced algebraic space factors through the
reduced induced closed subspace corresponding to `T` if and only if the image
of `Points Y` lands in `T`. -/
theorem factorsThrough_reduced_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) {Y : AlgebraicSpace S}
    (hY : hasEtaleLocal (IsReduced : ObjectProperty Scheme.{u}) Y)
    (g : Y ⟶ X) :
    (∃ h : Y ⟶ (ClosedSubspaceStructure.reduced T).space,
        h ≫ (ClosedSubspaceStructure.reduced T).ι = g) ↔
      Set.range (Points.map g) ⊆ (T : Set (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
