/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.CodimZero

/-!
# DVR uniqueness at codimension-zero points

The generic-image point and codimension-zero DVR uniqueness criterion are provided
by their shared mathematical owner.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq.sourceSpacePoint :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : ValuativeCommSq f), Points X)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq.sourceSpacePoint_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : ValuativeCommSq f),
    sq.sourceSpacePoint =
      fieldPointsToPoints
        (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom) sq.i₁)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.UniquenessAtCodimZero :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.UniquenessAtCodimZero.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    ValuativeCriterion.DVR.UniquenessAtCodimZero (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.UniquenessAtCodimZero.of_dvrUniqueness :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Uniqueness f], ValuativeCriterion.DVR.UniquenessAtCodimZero f)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.UniquenessAtCodimZero.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    ValuativeCriterion.DVR.UniquenessAtCodimZero f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        localRingDimAt sq.sourceSpacePoint = 0 → Subsingleton sq.commSq.LiftStruct)
