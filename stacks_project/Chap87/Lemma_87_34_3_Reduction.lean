/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Reduction of a formal algebraic space

This compatibility interface preserves the class-based reduction accessors and
their étale pullback specializations. Shared constructions use explicit reduction data.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- The algebraic-space reduction of a formal algebraic space, in the sense of
Lemma 87.12.1: a reduced algebraic space, a representable thickening into the
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
the reduced induced algebraic space of Definition 66.12.5. -/
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

/-- Lemma 87.12.1: the reduction is reduced, the structure morphism is a
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


/-- The legacy reduction interface supplies explicit canonical reduction data. -/
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

/-- The pullback of a reduction along an étale morphism is an algebraic space. -/
instance instIsAlgebraicSpace_pullback_reductionι
    {X Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [Reduction Y] (f : X ⟶ Y) [hf : Etale f] :
    AlgebraicSpace.IsAlgebraicSpace (pullback (reductionι Y) f) :=
  @AlgebraicSpace.IsAlgebraicSpace.pullback S X Y (reduction Y).functorOfPoints
    f hf.representable
    (AlgebraicSpace.instIsAlgebraicSpace_functorOfPoints (reduction Y)) (reductionι Y)

/-- The reduction along an étale morphism is its pullback over the target reduction. -/
def reductionAlong {X Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace S :=
  etalePullback f (reduction Y) (reductionι Y)

/-- The functor of points of the reduction along an étale morphism is the presheaf pullback. -/
theorem reductionAlong_functorOfPoints {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    (reductionAlong f).functorOfPoints = pullback (reductionι Y) f :=
  rfl

/-- The morphism to the domain is the second projection of the reduction pullback. -/
def reductionιAlong {X Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [Reduction Y] (f : X ⟶ Y) [Etale f] :
    (reductionAlong f).functorOfPoints ⟶ X :=
  pullback.snd (reductionι Y) f

/-- The inclusion along an étale morphism computes as the second pullback projection. -/
theorem reductionιAlong_snd {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    reductionιAlong f = pullback.snd (reductionι Y) f :=
  rfl

/-- The morphism to the target reduction is the first projection of the pullback. -/
def reductionMap {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] : reductionAlong f ⟶ reduction Y :=
  etalePullbackProjection f (reduction Y) (reductionι Y)

/-- The reduction map along an étale morphism computes as the first pullback projection. -/
theorem reductionMap_fst {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    reductionMap f = pullback.fst (reductionι Y) f :=
  rfl

/-- The projections from the reduction pullback form a cartesian square. -/
theorem reductionAlong_isPullback {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    IsPullback (reductionιAlong f) (reductionMap f) f (reductionι Y) :=
  (IsPullback.of_hasPullback (reductionι Y) f).flip

/-- The pullback over the target reduction is reduced. -/
theorem reductionAlong_isReduced {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [RY : Reduction Y]
    (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.hasEtaleLocal
      (IsReduced : ObjectProperty Scheme.{u}) (reductionAlong f) :=
  etalePullback_isReduced f (reduction Y) (reductionι Y) RY.isReduced

/-- The first projection from the reduction pullback is étale. -/
instance instEtale_reductionMap {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [Reduction Y]
    (f : X ⟶ Y) [Etale f] : AlgebraicSpace.Etale (reductionMap f) :=
  etalePullback_etale f (reduction Y) (reductionι Y)

end AlgebraicGeometry.FormalAlgebraicSpace
