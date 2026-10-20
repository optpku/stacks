/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Valuative tests on punctured normal curves

This leaf packages the normal integral curve-puncture configurations used in
valuative tests. The configuration itself does not require the base to be
Nagata; that hypothesis belongs to applications which identify the test with
separatedness or universal closedness.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A valuative square obtained from a punctured normal integral curve at a closed point with
one-dimensional local ring. -/
structure NormalCurvePunctureValuativeCommSq {S X Y : Scheme.{u}}
    (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y) where
  /-- The normal integral curve used for the test. -/
  C : Scheme.{u}
  /-- The structural map from the curve to the base. -/
  pC : C ⟶ S
  /-- The curve is of finite type over the base. -/
  [finiteType_pC : Scheme.Hom.FiniteType pC]
  /-- The curve is integral. -/
  [integral_C : IsIntegral C]
  /-- The curve is normal. -/
  normal : C.isNormal
  /-- The closed point removed from the curve. -/
  closedPoint : C
  /-- The chosen point is closed. -/
  closedPoint_mem : closedPoint ∈ closedPoints C
  /-- The local ring at the chosen closed point has Krull dimension one. -/
  stalkKrullDim : ringKrullDim (C.presheaf.stalk closedPoint) = 1
  /-- The punctured open complement of the chosen closed point. -/
  puncturedOpen : C.Opens
  /-- The prescribed open is exactly the complement of the chosen point. -/
  puncturedOpen_eq : (puncturedOpen : Set C) = ({closedPoint} : Set C)ᶜ
  /-- The map from the punctured curve to `X`. -/
  toX : puncturedOpen.toScheme ⟶ X
  /-- The map from the whole curve to `Y`. -/
  toY : C ⟶ Y
  /-- The two maps are compatible with `f`. -/
  fac_f : toX ≫ f = puncturedOpen.ι ≫ toY
  /-- The map to `X` is compatible with the base map. -/
  fac_pX : toX ≫ pX = puncturedOpen.ι ≫ pC
  /-- The map to `Y` is compatible with the base map. -/
  fac_pY : toY ≫ pY = pC
  /-- A fraction field of the local ring at the chosen point. -/
  K : Type u
  /-- The fraction field structure. -/
  [field_K : Field K]
  /-- The local-ring algebra structure on the fraction field. -/
  [algebra : Algebra (C.presheaf.stalk closedPoint) K]
  /-- The chosen field is a fraction field of the local ring. -/
  [isFractionRing : IsFractionRing (C.presheaf.stalk closedPoint) K]
  /-- The generic point of the local spectrum mapped into the punctured curve. -/
  genericToPuncturedOpen : Spec (CommRingCat.of K) ⟶ puncturedOpen.toScheme
  /-- Compatibility of the generic map with the canonical map from the local spectrum. -/
  genericToPuncturedOpen_fac : genericToPuncturedOpen ≫ puncturedOpen.ι =
    Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk closedPoint) K)) ≫
      C.fromSpecStalk closedPoint
  /-- The induced valuative commutative square over `f`. -/
  commSq : CommSq (genericToPuncturedOpen ≫ toX)
    (Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk closedPoint) K))) f
    (C.fromSpecStalk closedPoint ≫ toY)

namespace NormalCurvePunctureValuativeCommSq

/-- The induced commutative square over the tested morphism. -/
def targetSquare {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S} {f : X ⟶ Y}
    (sq : NormalCurvePunctureValuativeCommSq pX pY f) :=
  sq.commSq

end NormalCurvePunctureValuativeCommSq

/- Valuative criteria tested on punctured normal-curve configurations. -/
namespace NormalCurvePunctureValuativeCriterion

/-- Every punctured normal-curve test square over `f` admits a lift. -/
def Existence {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y) : Prop :=
  ∀ sq : NormalCurvePunctureValuativeCommSq pX pY f, sq.targetSquare.HasLift

/-- Every punctured normal-curve test square over `f` has at most one lift. -/
def Uniqueness {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y) : Prop :=
  ∀ sq : NormalCurvePunctureValuativeCommSq pX pY f,
    Subsingleton sq.targetSquare.LiftStruct

/-- Every punctured normal-curve test square over `f` has a lift and at most one lift. -/
def ExistsUnique {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y) : Prop :=
  ∀ sq : NormalCurvePunctureValuativeCommSq pX pY f,
    sq.targetSquare.HasLift ∧ Subsingleton sq.targetSquare.LiftStruct

/-- Normal-curve existence-and-uniqueness is equivalent to its separate existence and uniqueness
conditions. -/
theorem existsUnique_iff {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S} {f : X ⟶ Y} :
    ExistsUnique pX pY f ↔ Existence pX pY f ∧ Uniqueness pX pY f := sorry

/-- Normal-curve existence-and-uniqueness implies normal-curve existence. -/
theorem existence {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S} {f : X ⟶ Y}
    (h_criterion : ExistsUnique pX pY f) : Existence pX pY f := sorry

/-- Normal-curve existence-and-uniqueness implies normal-curve uniqueness. -/
theorem uniqueness {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S} {f : X ⟶ Y}
    (h_criterion : ExistsUnique pX pY f) : Uniqueness pX pY f := sorry

end NormalCurvePunctureValuativeCriterion

end AlgebraicGeometry
