/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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

namespace AlgebraicGeometry.AlgebraicSpace

/-- The closed immersion of the reduced induced structure on `T` maps Yoneda
sections into `T`. -/
theorem mapsInto_reducedι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) {U : (Over S)ᵒᵖ}
    (x : (ClosedSubspaceStructure.reduced T).space.functorOfPoints.obj U) :
    mapsInto (T : Set (Points X)) ((ClosedSubspaceStructure.reduced T).ι.app U x) :=
  sorry

namespace completionAlong

/-- The canonical morphism from the reduced induced closed subspace of `X`
corresponding to `T` into the completion of `X` along `T`. -/
def fromReduced {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X)) :
    (ClosedSubspaceStructure.reduced T).space.functorOfPoints ⟶
      completionAlong X T where
  app U :=
    ofHom fun x ↦
      ⟨(ClosedSubspaceStructure.reduced T).ι.app U x, mapsInto_reducedι T x⟩
  naturality := sorry

/-- Postcomposing `fromReduced T` with `ι X T` recovers the closed immersion of
the reduced induced structure on `T`. -/
theorem fromReduced_comp_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) :
    fromReduced T ≫ ι X T = (ClosedSubspaceStructure.reduced T).ι :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The completion of an algebraic space along a closed subset is a formal
algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    IsFormalAlgebraicSpace (AlgebraicSpace.completionAlong X T) :=
  sorry

/-- The canonical reduction of `completionAlong X T` is the reduced induced
closed subspace of `X` corresponding to `T`. -/
instance instReduction_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    Reduction (AlgebraicSpace.completionAlong X T) where
  space := (AlgebraicSpace.ClosedSubspaceStructure.reduced T).space
  ι := AlgebraicSpace.completionAlong.fromReduced T
  isReduced := sorry
  representable := sorry
  isThickening := sorry
  liftUnique := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
