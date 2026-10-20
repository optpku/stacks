/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.Presheaf.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Reduction of completion along a closed subset

The reduction of the completion of an algebraic space along a closed subset is
the reduced induced closed subspace, compatibly with the maps into the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Sections of the reduced induced closed subspace on `T` map into `T`. -/
theorem mapsInto_reducedι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) {U : (Over S)ᵒᵖ}
    (x : (ReducedClosed.Space.space X T).functorOfPoints.obj U) :
    mapsInto (T : Set (Points X)) ((ReducedClosed.Space.ι X T).app U x) :=
  sorry

namespace completionAlong

/-- The canonical morphism from the reduced induced closed subspace on `T`
into the completion along `T`. -/
def reducedι {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X)) :
    (ReducedClosed.Space.space X T).functorOfPoints ⟶
      completionAlong X T where
  app U :=
    ofHom fun x ↦
      ⟨(ReducedClosed.Space.ι X T).app U x, mapsInto_reducedι T x⟩
  naturality := sorry

/-- The canonical morphism from the reduced closed subspace to the completion
commutes with the inclusions into the ambient algebraic space. -/
theorem fromReduced_comp_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) :
    reducedι T ≫ ι X T = ReducedClosed.Space.ι X T := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The canonical morphism from the reduced closed subspace to the completion
is representable by algebraic spaces. -/
theorem fromReduced_representable {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) :
    representableByAlgebraicSpaces (reducedι T) :=
  sorry

/-- Every Yoneda pullback of the canonical morphism from the reduced closed
subspace to the completion is a thickening. -/
theorem fromReduced_isThickening {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X))
    (ha : representableByAlgebraicSpaces (reducedι T))
    {U : Over S} (ξ : yoneda.obj U ⟶ completionAlong X T) :
    IsThickening (representableByAlgebraicSpaces.pullbackHom ha ξ) :=
  sorry

/-- A morphism from a reduced algebraic space to the completion factors uniquely
through the reduced induced closed subspace. -/
theorem fromReduced_liftUnique {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) {U : AlgebraicSpace S}
    (hU : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ completionAlong X T) :
    ∃! h : U.functorOfPoints ⟶ (ReducedClosed.Space.space X T).functorOfPoints,
      h ≫ reducedι T = g :=
  sorry

end completionAlong

/-- The image of the reduction of the completion along `T` in the ambient
algebraic space is the reduced induced closed subspace on `T`. -/
theorem reduction_completionAlong {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    (SpacePresheaf.reduction (completionAlong X T)).image (completionAlong.ι X T) =
      Subfunctor.range (ClosedSubspaceStructure.reduced T).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The completion of an algebraic space along a closed subset is a formal
algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    IsFormalAlgebraicSpace (AlgebraicSpace.completionAlong X T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
