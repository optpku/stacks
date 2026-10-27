/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.AlgebraicSpace

/-!
# Class-based reductions of formal algebraic spaces

A reduction is a reduced algebraic space with a representable thickening and
the universal factorization property for maps from reduced algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- The algebraic-space reduction of a formal algebraic space consists of a reduced algebraic space, a representable thickening into the
formal algebraic space, and unique factorization of morphisms from reduced
algebraic spaces. -/
class Reduction (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] where
  /-- The underlying reduced algebraic space `X_red`. -/
  space : AlgebraicSpace S
  /-- The representable thickening `X_red ⟶ X`. -/
  ι : space.functorOfPoints ⟶ X
  /-- The reduction is reduced in the étale-local sense. -/
  isReduced : AlgebraicSpace.hasEtaleLocal
    (IsReduced : ObjectProperty Scheme.{u}) space
  /-- The structure morphism is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces ι
  /-- Yoneda pullbacks of the structure morphism are thickenings. -/
  isThickening : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ X),
    AlgebraicSpace.IsThickening
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)
  /-- A morphism from a reduced algebraic space into `X` factors uniquely
  through the reduction. -/
  liftUnique {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.hasEtaleLocal
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ X) :
    ∃! h : U.functorOfPoints ⟶ space.functorOfPoints, h ≫ ι = g

/-- The algebraic-space reduction of a formal algebraic space. -/
abbrev reduction (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : AlgebraicSpace S :=
  R.space

/-- The algebraic-space reduction is the `space` field of `Reduction`. -/
theorem reduction_def (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : reduction X = R.space :=
  rfl

/-- The canonical morphism from the reduction of a formal algebraic space. -/
abbrev reductionι (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : (reduction X).functorOfPoints ⟶ X :=
  R.ι

/-- The reduction morphism is the `ι` field of `Reduction`. -/
theorem reductionι_def (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : reductionι X = R.ι :=
  rfl

/-- The reduction of an algebraic space, viewed as a formal algebraic space, is
its reduced induced algebraic space. -/
instance instReduction_ofAlgebraicSpace (X : AlgebraicSpace S) :
    Reduction X.functorOfPoints where
  space := AlgebraicSpace.reduction X
  ι := AlgebraicSpace.reductionι X
  isReduced := isReduced_algebraicSpaceReduction X
  representable := AlgebraicSpace.representableByAlgebraicSpaces.of_hom
    (AlgebraicSpace.reductionι X)
  isThickening := fun {_} ξ ↦ isThickening_algebraicSpaceReductionι X ξ
  liftUnique := liftUnique_algebraicSpaceReduction X

/-- On an algebraic space, `reduction` recovers `AlgebraicSpace.reduction`. -/
theorem reduction_functorOfPoints (X : AlgebraicSpace S) :
    reduction X.functorOfPoints = AlgebraicSpace.reduction X :=
  rfl

/-- On an algebraic space, `reductionι` recovers `AlgebraicSpace.reductionι`. -/
theorem reductionι_functorOfPoints (X : AlgebraicSpace S) :
    reductionι X.functorOfPoints = AlgebraicSpace.reductionι X :=
  rfl

/-- The reduction is reduced, the structure morphism is a
representable thickening, and maps from reduced algebraic spaces factor
uniquely through it. -/
theorem reduction_spec (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] :
    AlgebraicSpace.hasEtaleLocal
        (IsReduced : ObjectProperty Scheme.{u}) (reduction X) ∧
      AlgebraicSpace.representableByAlgebraicSpaces (reductionι X) ∧
        (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ X),
          AlgebraicSpace.IsThickening
            (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
              R.representable ξ)) ∧
          ∀ {U : AlgebraicSpace S}
            (hU : AlgebraicSpace.hasEtaleLocal
              (IsReduced : ObjectProperty Scheme.{u}) U)
            (g : U.functorOfPoints ⟶ X),
            ∃! h : U.functorOfPoints ⟶ (reduction X).functorOfPoints,
              h ≫ reductionι X = g :=
  ⟨R.isReduced, R.representable, R.isThickening, fun {_} hU g ↦ R.liftUnique hU g⟩


/-- A reduction supplies explicit canonical reduction data. -/
def Reduction.toReductionData {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : Reduction X) : ReductionData X where
  space := R.space
  ι := R.ι
  isReduced := R.isReduced
  representable := R.representable
  isThickening := fun {_} ξ ↦
    ⟨(R.isThickening ξ).toIsClosedImmersion,
      (R.isThickening ξ).toSurjective.map_surjective⟩
  liftUnique := R.liftUnique

end AlgebraicGeometry.FormalAlgebraicSpace
