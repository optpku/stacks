/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Class
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

/- The algebraic-space reduction of a formal algebraic space, in the sense of
Lemma 87.12.1: a reduced algebraic space, a representable thickening into the
formal algebraic space, and unique factorization of morphisms from reduced
algebraic spaces. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Reduction :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X],
    Type (u + 1))

/- The algebraic-space reduction of a formal algebraic space. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.reduction :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X],
    AlgebraicSpace S)

/- The algebraic-space reduction is the `space` field of `Reduction`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.reduction_def :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X],
    reduction X = R.space)

/- The canonical morphism from the reduction of a formal algebraic space. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.reductionι :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X],
    (reduction X).functorOfPoints ⟶ X)

/- The reduction morphism is the `ι` field of `Reduction`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.reductionι_def :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X],
    reductionι X = R.ι)

/- The reduction of an algebraic space, viewed as a formal algebraic space, is
the reduced induced algebraic space of Definition 66.12.5. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.instReduction_ofAlgebraicSpace :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Reduction X.functorOfPoints)

/- On an algebraic space, `reduction` recovers `AlgebraicSpace.reduction`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.reduction_functorOfPoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    reduction X.functorOfPoints = AlgebraicSpace.reduction X)

/- On an algebraic space, `reductionι` recovers `AlgebraicSpace.reductionι`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.reductionι_functorOfPoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    reductionι X.functorOfPoints = AlgebraicSpace.reductionι X)

/- Lemma 87.12.1: the reduction is reduced, the structure morphism is a
representable thickening, and maps from reduced algebraic spaces factor
uniquely through it. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.reduction_spec :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X],
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
              h ≫ reductionι X = g)

/- The legacy reduction interface supplies explicit canonical reduction data. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Reduction.toReductionData :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : Reduction X),
    ReductionData X)

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
