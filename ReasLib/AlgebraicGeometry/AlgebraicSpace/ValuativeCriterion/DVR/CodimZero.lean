/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints

/-!
# DVR existence and uniqueness at codimension-zero points

Existence and uniqueness of dotted lifts for discrete valuation ring valuative
squares can be restricted to those whose generic image is a point of local-ring
dimension `0`. The DVR valuative criterion at these points combines both conditions.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCommSq

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

/-- The image in `|X|` of the generic map `Spec(K) ⟶ X` of a valuative square. -/
def sourceSpacePoint (sq : ValuativeCommSq f) : Points X :=
  fieldPointsToPoints
    (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom) sq.i₁

/-- `sourceSpacePoint` is the field-valued point of `X` associated to `Spec(K) ⟶ X`. -/
theorem sourceSpacePoint_eq (sq : ValuativeCommSq f) :
    sourceSpacePoint sq =
      fieldPointsToPoints
        (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom) sq.i₁ :=
  sorry

end ValuativeCommSq

/-- A morphism of algebraic spaces satisfies uniqueness of dotted lifts for DVR
valuative squares whose image of `Spec(K) ⟶ X` has local-ring dimension `0`. -/
@[mk_iff]
class ValuativeCriterion.DVR.UniquenessAtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square with generic image of local-ring dimension `0` has at most
  one dotted lift. -/
  subsingleton_liftStruct :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      localRingDimAt sq.sourceSpacePoint = 0 → Subsingleton sq.commSq.LiftStruct

namespace ValuativeCriterion.DVR.UniquenessAtCodimZero

/-- The identity morphism of an algebraic space satisfies DVR uniqueness at
codimension-zero points. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : UniquenessAtCodimZero (𝟙 X) := sorry

/-- Uniqueness for all DVR valuative squares implies uniqueness for those whose generic
image has local-ring dimension `0`. -/
instance of_dvrUniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Uniqueness f] : UniquenessAtCodimZero f := sorry

/-- A morphism satisfies DVR uniqueness at codimension-zero points if and only if every
DVR valuative square whose generic image has local-ring dimension `0` has at most one
lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    UniquenessAtCodimZero f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        localRingDimAt sq.sourceSpacePoint = 0 → Subsingleton sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion.DVR.UniquenessAtCodimZero


/-- A morphism of algebraic spaces satisfies existence of dotted lifts for DVR
valuative squares whose image of `Spec(K) ⟶ X` has local-ring dimension `0`. -/
@[mk_iff]
class ValuativeCriterion.DVR.ExistenceAtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square with generic image of local-ring dimension `0` has a
  dotted lift. -/
  nonempty_liftStruct :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      localRingDimAt sq.sourceSpacePoint = 0 → Nonempty sq.commSq.LiftStruct

namespace ValuativeCriterion.DVR.ExistenceAtCodimZero

/-- The identity morphism of an algebraic space satisfies DVR existence at
codimension-zero points. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : ExistenceAtCodimZero (𝟙 X) := sorry

/-- Existence for all DVR valuative squares implies existence for those whose generic
image has local-ring dimension `0`. -/
instance of_dvrExistence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f] : ExistenceAtCodimZero f := sorry

/-- A morphism satisfies DVR existence at codimension-zero points if and only if every
DVR valuative square whose generic image has local-ring dimension `0` has a lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ExistenceAtCodimZero f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        localRingDimAt sq.sourceSpacePoint = 0 → Nonempty sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion.DVR.ExistenceAtCodimZero

/-- A morphism of algebraic spaces satisfies the DVR valuative criterion at
codimension-zero points if every DVR valuative square whose image of
`Spec(K) ⟶ X` has local-ring dimension `0` has a unique lift. -/
@[mk_iff]
class ValuativeCriterion.DVR.AtCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop
    extends ValuativeCriterion.DVR.UniquenessAtCodimZero f,
      ValuativeCriterion.DVR.ExistenceAtCodimZero f

namespace ValuativeCriterion.DVR.AtCodimZero

/-- The identity morphism of an algebraic space satisfies the DVR valuative
criterion at codimension-zero points. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : AtCodimZero (𝟙 X) := sorry

/-- The DVR valuative criterion implies the DVR valuative criterion at
codimension-zero points. -/
instance of_dvr {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR f] : AtCodimZero f := sorry

/-- A morphism satisfies the DVR valuative criterion at codimension-zero points if and
only if it satisfies both the uniqueness and existence parts at those points. -/
theorem iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    AtCodimZero f ↔
      ValuativeCriterion.DVR.UniquenessAtCodimZero f ∧
        ValuativeCriterion.DVR.ExistenceAtCodimZero f :=
  sorry

/-- A morphism satisfies the DVR valuative criterion at codimension-zero points if and
only if every DVR valuative square whose generic image has local-ring dimension `0`
has a unique lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    AtCodimZero f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        localRingDimAt sq.sourceSpacePoint = 0 →
          Nonempty sq.commSq.LiftStruct ∧ Subsingleton sq.commSq.LiftStruct :=
  sorry

/-- A morphism satisfying the DVR valuative criterion at codimension-zero points has a
unique dotted lift on every such DVR valuative square. -/
theorem unique_liftStruct {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AtCodimZero f] (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R)
    (h0 : localRingDimAt sq.sourceSpacePoint = 0) :
    Nonempty (Unique sq.commSq.LiftStruct) :=
  sorry

end ValuativeCriterion.DVR.AtCodimZero

end AlgebraicGeometry.AlgebraicSpace
