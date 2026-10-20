/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction

/-!
# Canonical reduction data for completions

The reduced induced closed subspace on a closed subset is the canonical
reduction of the completion along that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- The reduced induced closed subspace on `T`, with its canonical inclusion,
is reduction data for the completion of `X` along `T`. -/
def reductionData {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    FormalAlgebraicSpace.ReductionData (completionAlong X T) where
  space := ReducedClosed.Space.space X T
  ι := reducedι T
  isReduced := ReducedClosed.Construction.actual_reduced X T
  representable := fromReduced_representable T
  isThickening := by
    intro U ξ
    have h := fromReduced_isThickening T (fromReduced_representable T) ξ
    exact ⟨h.toIsClosedImmersion, h.toSurjective.map_surjective⟩
  liftUnique := by
    intro U hU g
    exact fromReduced_liftUnique T hU g

/-- The underlying space of the canonical reduction of a completion is the
reduced induced closed subspace on the closed subset. -/
theorem reductionData_space {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    (reductionData X T).space = ReducedClosed.Space.space X T :=
  rfl

/-- The inclusion of the canonical reduction into a completion is the canonical
morphism from the reduced induced closed subspace. -/
theorem reductionData_ι {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    (reductionData X T).ι = reducedι T :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.completionAlong
