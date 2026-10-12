/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import stacks_project.Chap67.Definition_67_47_3_RationalFunction
public import stacks_project.Chap67.Lemma_67_10_8
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Definition_72_5_2_ResidueField

/-!
# Canonical evaluation at an integral algebraic space's generic point

Rational functions are evaluated on their actual dense-open representatives.
Elementary-neighbourhood sections are evaluated along the canonical comparison
of their monomorphic residue points, then descend through the henselian colimit.
Every inverse is the inverse of a specified map; no unrelated isomorphism is chosen.
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

/-- This fixed projection is invertible: elementary residue points are monomorphic,
the two representatives have the same point, and a nonempty monomorphism to a field
spectrum is an isomorphism (Lemma 67.10.8). -/
theorem elementaryProjection_isIso {X : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) : IsIso (elementaryProjection U) :=
  sorry

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

/-- A generic point lies in every dense open, so this particular base-changed open
immersion is an isomorphism. This statement is not valid for arbitrary points. -/
theorem domainProjection_isIso {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (f : PartialMap X (affineLine S)) :
    IsIso (domainInfFst (X.fromSpecResidueField η) f.domain.hom) :=
  sorry

/-- The canonical identification of the preimage of a dense open with the generic-point spectrum. -/
def domainProjectionIso {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (f : PartialMap X (affineLine S)) :=
  @asIso _ _ _ _ (domainInfFst (X.fromSpecResidueField η) f.domain.hom)
    (domainProjection_isIso hη f)

/-- Lift the actual generic-point morphism into the actual domain of a partial map. -/
def domainLift {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (f : PartialMap X (affineLine S)) :
    ofOver (residueSpecOver η) ⟶ f.domain.left :=
  (domainProjectionIso hη f).inv ≫ domainInfSnd (X.fromSpecResidueField η) f.domain.hom

/-- The canonical domain lift factors the specified generic-point morphism. -/
theorem domainLift_over {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (f : PartialMap X (affineLine S)) :
    domainLift hη f ≫ f.domain.hom = X.fromSpecResidueField η :=
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

/-- Evaluate a partial function by lifting the generic point into its domain,
then extracting the actual affine-line coordinate and applying ΓSpecIso. -/
def PartialMap.evaluateGeneric {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (f : PartialMap X (affineLine S)) :
    X.residueField η :=
  (Scheme.ΓSpecIso (X.residueField η)).hom
    (coordHom (yonedaEquiv (GenericPointComparison.domainLift hη f ≫ f.hom)))

/-- Agreement on a further dense open gives equal evaluations at the generic point. -/
theorem PartialMap.evaluateGeneric_equiv {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) {f g : PartialMap X (affineLine S)}
    (h : f.equiv g) : f.evaluateGeneric hη = g.evaluateGeneric hη :=
  sorry

/-- The rational-function evaluation homomorphism is quotient descent of actual partial evaluation. -/
def rationalFunctionRingToResidueField {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) :
    RationalFunction X →+* ULift.{u + 1} (X.residueField η) where
  toFun := Quotient.lift (fun f ↦ ULift.up (f.evaluateGeneric hη))
    (fun _ _ h ↦ congrArg ULift.up (PartialMap.evaluateGeneric_equiv hη h))
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation on a quotient representative is exactly its partial-map evaluation. -/
theorem rationalFunctionRingToResidueField_rep {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (f : PartialMap X (affineLine S)) :
    rationalFunctionRingToResidueField hη f.toRationalMap = ULift.up (f.evaluateGeneric hη) :=
  rfl

/-- The specified evaluation is invertible: on a schematic neighbourhood of the
generic point it is the usual rational-function/stalk-residue comparison. -/
theorem rationalFunctionRingToResidueField_isIso {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) :
    IsIso (CommRingCat.ofHom (rationalFunctionRingToResidueField hη)) :=
  sorry

/-- Canonical rational-function/residue-field equivalence, with its forward map fixed by evaluation. -/
def rationalFunctionRingEquivResidueField {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) :
    RationalFunction X ≃+* ULift.{u + 1} (X.residueField η) :=
  (@asIso _ _ _ _ (CommRingCat.ofHom (rationalFunctionRingToResidueField hη))
    (rationalFunctionRingToResidueField_isIso hη)).commRingCatIsoToRingEquiv

/-- The rational-function equivalence retains the explicitly constructed evaluation. -/
theorem rationalFunctionRingEquivResidueField_apply {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (a : RationalFunction X) :
    rationalFunctionRingEquivResidueField hη a = rationalFunctionRingToResidueField hη a :=
  rfl

/-- The canonical identification through the common residue-field comparison. -/
def rationalFunctionRingEquivHenselianLocalRing {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) :
    RationalFunction X ≃+* henselianLocalRing X η :=
  (rationalFunctionRingEquivResidueField hη).trans
    (henselianLocalRingEquivResidueField hη).symm

/-- These fixed comparisons form a commuting triangle. -/
theorem rationalFunctionRingEquivResidueField_trans {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) :
    (rationalFunctionRingEquivHenselianLocalRing hη).trans
      (henselianLocalRingEquivResidueField hη) = rationalFunctionRingEquivResidueField hη := by
  apply RingEquiv.ext
  intro a
  exact (henselianLocalRingEquivResidueField hη).apply_symm_apply _

/-- The rational-function ring is nontrivial since an integral space is nonempty and reduced. -/
instance nontrivialRationalFunction {X : AlgebraicSpace S} [IsIntegral X] :
    Nontrivial (RationalFunction X) :=
  sorry

/-- A nonzero rational function on an integral space is a unit: invert it on its
dense open nonvanishing locus. This proposition does not select a generic point. -/
theorem rationalFunction_isUnit_of_ne_zero {X : AlgebraicSpace S} [IsIntegral X]
    (f : RationalFunction X) (hf : f ≠ 0) : IsUnit f :=
  sorry

/-- The canonical total ring inverse makes rational functions a field without choosing a point. -/
instance instField_rationalFunctionRing {X : AlgebraicSpace S} [IsIntegral X] :
    Field (RationalFunction X) where
  inv := Ring.inverse
  nnqsmul := _
  qsmul := _
  mul_inv_cancel f hf := Ring.mul_inverse_cancel f (rationalFunction_isUnit_of_ne_zero f hf)
  inv_zero := Ring.inverse_zero _
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩

/-- The henselian local ring at a specified generic point is nontrivial. -/
theorem henselianLocalRing_nontrivial_generic {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) : Nontrivial (henselianLocalRing X η) :=
  sorry

/-- Every nonzero element of the generic henselian local ring is a unit. -/
theorem henselianLocalRing_isUnit_generic {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) (a : henselianLocalRing X η)
    (ha : a ≠ 0) : IsUnit a :=
  sorry

/-- Field structure at a specified generic point, taking its ordinary membership proof
explicitly instead of requiring a manufactured Fact instance. -/
@[reducible] def field_henselianLocalRing_genericPoint {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X) : Field (henselianLocalRing X η) where
  inv := Ring.inverse
  nnqsmul := _
  qsmul := _
  mul_inv_cancel a ha := Ring.mul_inverse_cancel a (henselianLocalRing_isUnit_generic hη a ha)
  inv_zero := Ring.inverse_zero _
  exists_pair_ne := (henselianLocalRing_nontrivial_generic hη).exists_pair_ne

end AlgebraicGeometry.AlgebraicSpace
