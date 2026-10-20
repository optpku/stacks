/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Basic

/-!
# Rational functions at generic points of integral algebraic spaces

Evaluation of dense-open representatives identifies the rational-function ring
with the residue field and the henselian local ring at a generic point. These
comparisons give a commuting triangle of canonical ring equivalences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace GenericPointComparison

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

end AlgebraicGeometry.AlgebraicSpace
