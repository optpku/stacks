/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure

/-!
# Reduction of completion of formal algebraic spaces

The reduced induced closed subspace on a closed subset of a reduction is the
reduction of the completion along that subset, with its canonical inclusion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace (Points ClosedSubspaceStructure)

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Recompletion

variable {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
  [IsFormalAlgebraicSpace X] (R : ReductionData X)

/-- Sections of the reduced induced closed subspace have reduced image in the
specified closed subset of the reduction. -/
private theorem mapsInto_fromReduced (T : Closeds (Points R.space))
    {U : (Over S)ᵒᵖ}
    (z : (ClosedSubspaceStructure.reduced T).space.functorOfPoints.obj U) :
    mapsInto R (T : Set (Points R.space))
      ((NatTrans.vcomp (ClosedSubspaceStructure.reduced T).ι R.ι).app U z) :=
  sorry

/-- The canonical morphism from the reduced induced closed subspace to the
completion sends each section to its composite into the ambient formal space. -/
@[no_expose]
def fromReduced (T : Closeds (Points R.space)) :
    (ClosedSubspaceStructure.reduced T).space.functorOfPoints ⟶ functor R T where
  app U := ofHom fun z ↦
    ⟨(NatTrans.vcomp (ClosedSubspaceStructure.reduced T).ι R.ι).app U z,
      mapsInto_fromReduced R T z⟩
  naturality := sorry

/-- The underlying section of the canonical morphism to the completion is the
composite through the reduced induced inclusion and the reduction inclusion. -/
theorem fromReduced_app (T : Closeds (Points R.space)) (U : (Over S)ᵒᵖ)
    (z : (ClosedSubspaceStructure.reduced T).space.functorOfPoints.obj U) :
    ((fromReduced R T).app U z).val =
      (NatTrans.vcomp (ClosedSubspaceStructure.reduced T).ι R.ι).app U z := by
  rfl

/-- Composing the canonical morphism to the completion with its inclusion
recovers the composite into the ambient formal space. -/
theorem fromReduced_comp_ι (T : Closeds (Points R.space)) :
    fromReduced R T ≫ ι R T =
      NatTrans.vcomp (ClosedSubspaceStructure.reduced T).ι R.ι := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- The canonical morphism from the reduced induced closed subspace to the
completion is representable by algebraic spaces. -/
theorem fromReduced_representable (T : Closeds (Points R.space)) :
    AlgebraicSpace.representableByAlgebraicSpaces (fromReduced R T) :=
  sorry

/-- Every Yoneda pullback of the canonical morphism to the completion is a
closed immersion surjective on points. -/
theorem fromReduced_isThickening (T : Closeds (Points R.space))
    {U : Over S} (ξ : yoneda.obj U ⟶ functor R T) :
    AlgebraicSpace.IsClosedImmersion
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
        (fromReduced_representable R T) ξ) ∧
      Function.Surjective
        (Points.map (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
          (fromReduced_representable R T) ξ)) :=
  sorry

/-- A morphism from a reduced algebraic space to the completion factors uniquely
through the reduced induced closed subspace. -/
theorem fromReduced_liftUnique (T : Closeds (Points R.space)) {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ functor R T) :
    ∃! h : U.functorOfPoints ⟶ (ClosedSubspaceStructure.reduced T).space.functorOfPoints,
      h ≫ fromReduced R T = g :=
  sorry

/-- The reduced induced closed subspace, with its canonical morphism to the
completion, is reduction data for the completion. -/
def reductionData (T : Closeds (Points R.space)) :
    @ReductionData S (functor R T) (isFormalAlgebraicSpace R T) :=
  @ReductionData.mk S (functor R T) (isFormalAlgebraicSpace R T)
    (ClosedSubspaceStructure.reduced T).space (fromReduced R T)
    (AlgebraicSpace.ReducedClosed.Construction.actual_reduced R.space T)
    (fromReduced_representable R T)
    (fun ⦃U⦄ ξ ↦ fromReduced_isThickening R T (U := U) ξ)
    (fun {U} hU g ↦ fromReduced_liftUnique R T (U := U) hU g)

/-- The algebraic space projected from the canonical reduction data of the
completion. -/
def reductionSpace (T : Closeds (Points R.space)) : AlgebraicSpace S :=
  @ReductionData.space S (functor R T) (isFormalAlgebraicSpace R T) (reductionData R T)

/-- The inclusion projected from the canonical reduction data of the completion. -/
def reductionι (T : Closeds (Points R.space)) :
    (reductionSpace R T).functorOfPoints ⟶ functor R T :=
  @ReductionData.ι S (functor R T) (isFormalAlgebraicSpace R T) (reductionData R T)

end Recompletion

/-- The reduction of the completion along a closed subset is the reduced induced
closed subspace of the reduction on that subset. -/
theorem reduction_completionAlong {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) (T : Closeds (Points R.space)) :
    Recompletion.reductionSpace R T = (ClosedSubspaceStructure.reduced T).space :=
  rfl

/-- The reduction inclusion of the completion is the canonical morphism from
the reduced induced closed subspace. -/
theorem reductionι_completionAlong {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) (T : Closeds (Points R.space)) :
    Recompletion.reductionι R T = Recompletion.fromReduced R T :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace
