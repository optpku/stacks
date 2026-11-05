/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism.Field
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField

/-!
# Residue evaluation and henselian local rings at generic points

Evaluation on elementary étale neighbourhoods induces the canonical map from the
henselian local ring to the residue field. At a generic point of an integral
algebraic space this map is an isomorphism and the henselian local ring is a field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The canonical residue-field spectrum, with its actual map to the base. -/
def residueSpecOver {X : AlgebraicSpace S} [IsDecent X] (x : Points X) : Over S :=
  (FieldValuedPoint.residuePoint x).overObj

namespace GenericPointComparison

/-- The first projection from the intersection of the two specified residue points. -/
def elementaryProjection {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :=
  domainInfFst (X.fromSpecResidueField x) (EtaleNeighborhood.residueHom U.obj)

set_option backward.isDefEq.respectTransparency false in
/-- The two residue points represent the same point. Their unique factorization
gives a section of this monomorphic projection, hence an inverse. -/
theorem elementaryProjection_isIso {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) : IsIso (elementaryProjection U) := by
  letI : Mono (EtaleNeighborhood.residueHom U.obj) := U.property
  have hp : Points.mk (EtaleNeighborhood.residuePoint U.obj) = x := by
    change Points.mapOfOver U.obj.hom U.obj.point = x
    exact U.obj.2.2
  have heq : Points.mk (FieldValuedPoint.residuePoint x) =
      Points.mk (EtaleNeighborhood.residuePoint U.obj) :=
    (FieldValuedPoint.mk_residuePoint x).trans hp.symm
  obtain ⟨φ⟩ := (FieldValuedPoint.unique_factorization_of_mono
    (p := FieldValuedPoint.residuePoint x)
    (q := EtaleNeighborhood.residuePoint U.obj) U.property heq).1
  let r : ofOver (FieldValuedPoint.residuePoint x).overObj ⟶
      ofOver (EtaleNeighborhood.residuePoint U.obj).overObj :=
    ofOverHomMk φ.schemeHom φ.fac_structure
  have hr : r ≫ EtaleNeighborhood.residueHom U.obj = X.fromSpecResidueField x :=
    φ.fac_hom
  let s := ReasLibPullback.pullbackLift (X.fromSpecResidueField x)
    (EtaleNeighborhood.residueHom U.obj) (𝟙 _) r (by rw [Category.id_comp]; exact hr.symm)
  have hs : s ≫ elementaryProjection U = 𝟙 _ :=
    ReasLibPullback.pullbackLift_fst _ _ _ _ _
  letI : Mono (elementaryProjection U) :=
    (ReasLibPullback.isPullback (X.fromSpecResidueField x)
      (EtaleNeighborhood.residueHom U.obj)).mono_fst_of_mono
  exact ⟨⟨s, (cancel_mono (elementaryProjection U)).mp (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp]), hs⟩⟩

/-- The isomorphism attached to the actual residue-point intersection projection. -/
def elementaryProjectionIso {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :=
  @asIso _ _ _ _ (elementaryProjection U) (elementaryProjection_isIso U)

/-- The canonical map from the residue-field point to the selected elementary residue point. -/
def elementaryResidueMap {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :
    ofOver (residueSpecOver x) ⟶ ofOver (EtaleNeighborhood.residuePoint U.obj).overObj :=
  (elementaryProjectionIso U).inv ≫
    domainInfSnd (X.fromSpecResidueField x) (EtaleNeighborhood.residueHom U.obj)

/-- The residue comparison is over X, not over an unrelated base-point field. -/
theorem elementaryResidueMap_over {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :
    elementaryResidueMap U ≫ EtaleNeighborhood.residueHom U.obj = X.fromSpecResidueField x :=
  sorry

end GenericPointComparison

/-- The scheme morphism from κ(x) to the selected elementary neighbourhood, extracted
by Yoneda from the fixed pullback comparison, followed by its scheme residue-point map. -/
def residueSchemeHom {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :
    Spec (X.residueField x) ⟶ (EtaleNeighborhood.Elementary.toScheme X x).obj U :=
  (yonedaEquiv (GenericPointComparison.elementaryResidueMap U)).left ≫
    (Scheme.FieldValuedPoint.residuePoint U.obj.point).hom

/-- Evaluate a section along the actual κ(x)-valued point of the elementary neighbourhood. -/
def elementaryEvaluation {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :
    Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) →+* X.residueField x :=
  (Scheme.ΓSpecIso (X.residueField x)).hom.hom.comp
    (Scheme.Γ.map (residueSchemeHom U).op).hom

/-- Lift elementary evaluation into the universe of the defining henselian colimit. -/
def elementaryEvaluationLift {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :
    Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) →+*
      ULift.{u + 1} (X.residueField x) :=
  ULift.ringEquiv.symm.toRingHom.comp (elementaryEvaluation U)

/-- The evaluation cocone on the actual elementary-neighbourhood sections diagram. -/
def elementaryEvaluationCocone {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    Cocone (EtaleNeighborhood.Elementary.sections X x) where
  pt := (CommRingCat.universeLift.{u, u + 1}).obj (X.residueField x)
  ι :=
    { app := fun j ↦ (CommRingCat.universeLift.{u, u + 1}).map
        (CommRingCat.ofHom (elementaryEvaluation (ULiftHom.objDown j).unop))
      naturality := sorry }

/-- The canonical residue map is induced by evaluation on each actual elementary neighbourhood. -/
def henselianLocalRingToResidueField {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    henselianLocalRing X x →+* ULift.{u + 1} (X.residueField x) :=
  (colimit.desc (EtaleNeighborhood.Elementary.sections X x)
    (elementaryEvaluationCocone x)).hom

/-- The residue map agrees with section evaluation on every canonical colimit coprojection. -/
theorem henselianLocalRingToResidueField_comp_ι {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (U : EtaleNeighborhood.Elementary X x) :
    (henselianLocalRingToResidueField x).comp (henselianLocalRing.ι X x U) =
      elementaryEvaluationLift U := by
  apply RingHom.ext
  intro s
  change ((colimit.ι (EtaleNeighborhood.Elementary.sections X x) (ULiftHom.objUp (op U)) ≫
    colimit.desc (EtaleNeighborhood.Elementary.sections X x)
      (elementaryEvaluationCocone x)).hom (ULift.up s)) = _
  rw [colimit.ι_desc]
  rfl

/-- At a generic point the local ring is a field and its henselization is itself;
therefore this specified residue map, rather than an arbitrary isomorphism, is invertible. -/
theorem henselianLocalRingToResidueField_isIso {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) :
    IsIso (CommRingCat.ofHom (henselianLocalRingToResidueField η)) :=
  sorry

/-- Canonical identification, with the forward map fixed by the henselian colimit evaluation. -/
def henselianLocalRingEquivResidueField {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) :
    henselianLocalRing X η ≃+* ULift.{u + 1} (X.residueField η) :=
  (@asIso _ _ _ _ (CommRingCat.ofHom (henselianLocalRingToResidueField η))
    (henselianLocalRingToResidueField_isIso hη)).commRingCatIsoToRingEquiv

/-- The forward henselian equivalence is exactly the named colimit-induced map. -/
theorem henselianLocalRingEquivResidueField_apply {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (a : henselianLocalRing X η) :
    henselianLocalRingEquivResidueField hη a = henselianLocalRingToResidueField η a :=
  rfl

/-- The henselian local ring at a specified generic point is nontrivial. -/
theorem henselianLocalRing_nontrivial_generic {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) : Nontrivial (henselianLocalRing X η) :=
  sorry

/-- Every nonzero element of the generic henselian local ring is a unit. -/
theorem henselianLocalRing_isUnit_generic {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (a : henselianLocalRing X η)
    (ha : a ≠ 0) : IsUnit a :=
  sorry

/-- The henselian local ring at a specified generic point carries a field structure. -/
@[reducible] def field_henselianLocalRing_genericPoint {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) : Field (henselianLocalRing X η) where
  inv := Ring.inverse
  nnqsmul := _
  qsmul := _
  mul_inv_cancel a ha := Ring.mul_inverse_cancel a (henselianLocalRing_isUnit_generic hη a ha)
  inv_zero := Ring.inverse_zero _
  exists_pair_ne := (henselianLocalRing_nontrivial_generic hη).exists_pair_ne

end AlgebraicGeometry.AlgebraicSpace
