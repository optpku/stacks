module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Reduction
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap87.Definition_87_25_1_Surjective
public import stacks_project.Chap87.Lemma_87_14_4_Completion

/-!
# Reduction of the completion along a closed subset

The completion `completionAlong X T` of an algebraic space along a closed
subset is a formal algebraic space whose algebraic-space reduction is the
reduced induced closed subspace corresponding to `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- The canonical morphism from the reduced induced closed-subspace structure
on `T` into the completion along `T`. -/
def fromReduced {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X)) :
    (ClosedSubspaceStructure.reduced T).space.functorOfPoints ⟶ completionAlong X T :=
  reducedι T

end AlgebraicGeometry.AlgebraicSpace.completionAlong

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The canonical reduction of `completionAlong X T` is the reduced induced
closed subspace of `X` corresponding to `T`. -/
instance instReduction_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    Reduction (AlgebraicSpace.completionAlong X T) where
  space := AlgebraicSpace.ReducedClosed.Space.space X T
  ι := AlgebraicSpace.completionAlong.reducedι T
  isReduced := AlgebraicSpace.ReducedClosed.Construction.actual_reduced X T
  representable := AlgebraicSpace.completionAlong.fromReduced_representable T
  isThickening := fun {_} ξ ↦
    AlgebraicSpace.completionAlong.fromReduced_isThickening T
      (AlgebraicSpace.completionAlong.fromReduced_representable T) ξ
  liftUnique := AlgebraicSpace.completionAlong.fromReduced_liftUnique T

end AlgebraicGeometry.FormalAlgebraicSpace
