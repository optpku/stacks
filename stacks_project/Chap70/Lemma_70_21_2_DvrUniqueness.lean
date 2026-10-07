module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap69.Lemma_69_19_1_DVR

/-!
# DVR uniqueness at codimension-zero points

A morphism of algebraic spaces satisfies uniqueness of dotted lifts for discrete
valuation ring valuative squares whose generic image is a point of local-ring
dimension `0`.
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

end AlgebraicGeometry.AlgebraicSpace
