/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.IsTensorProduct
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk

/-!
# Local rings of scheme-theoretic fibres

The stalk of a scheme-theoretic fibre at the distinguished point determined by a
source point is canonically isomorphic to the quotient of the source stalk by
the extended maximal ideal of the target stalk, and to the residue-field tensor
product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The extended maximal ideal `𝔪_{f(x)} 𝒪_{X, x}` of the source stalk. -/
abbrev sourceStalkBaseMaximalIdeal {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  (maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom

/-- The quotient `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}`. -/
abbrev sourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Type u :=
  X.presheaf.stalk x ⧸ sourceStalkBaseMaximalIdeal f x

/-- The quotient `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}` is a local ring. -/
noncomputable instance instIsLocalRing_sourceStalkQuotient
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsLocalRing (sourceStalkQuotient f x) :=
  @IsLocalRing.of_surjective' _ _ _ _ _
    (Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (f.stalkMap x).hom).ne)
    (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x))
    (Ideal.Quotient.mk_surjective)

/-- The tensor product `𝒪_{X, x} ⊗_{𝒪_{S, f(x)}} κ(f(x))`. -/
abbrev sourceStalkTensorResidueField {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Type u :=
  X.presheaf.stalk x ⊗[S.presheaf.stalk (f x)] S.residueField (f x)

/-- The canonical map `𝒪_{S, f(x)} → 𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}` kills the
maximal ideal of the target stalk. -/
theorem algebraMap_sourceStalkQuotient_eq_zero_of_mem_maximalIdeal
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (r : S.presheaf.stalk (f x)) (hr : r ∈ maximalIdeal (S.presheaf.stalk (f x))) :
    ((Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x)).comp (f.stalkMap x).hom) r = 0 :=
  by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)

/-- The induced ring homomorphism `κ(f(x)) → 𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}`. -/
noncomputable def residueFieldToSourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    S.residueField (f x) →+* sourceStalkQuotient f x :=
  Ideal.Quotient.lift (maximalIdeal (S.presheaf.stalk (f x)))
    ((Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x)).comp (f.stalkMap x).hom)
    (algebraMap_sourceStalkQuotient_eq_zero_of_mem_maximalIdeal f x)

/-- The induced map sends the residue of a target-stalk element to the class of
its image in the source stalk. -/
theorem residueFieldToSourceStalkQuotient_residue {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (r : S.presheaf.stalk (f x)) :
    residueFieldToSourceStalkQuotient f x ((S.residue (f x)).hom r) =
      Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x) ((f.stalkMap x).hom r) :=
  rfl

/-- The morphism `Spec(𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}) ⟶ X` induced by the
quotient of the source stalk. -/
noncomputable def fromSpecSourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec (CommRingCat.of (sourceStalkQuotient f x)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x))) ≫
    X.fromSpecStalk x

/-- The morphism `Spec(𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}) ⟶ Spec κ(f(x))` induced
by the residue-field action on the quotient. -/
noncomputable def fromSpecSourceStalkQuotientToSpecResidueField {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    Spec (CommRingCat.of (sourceStalkQuotient f x)) ⟶ Spec (S.residueField (f x)) :=
  Spec.map (CommRingCat.ofHom (residueFieldToSourceStalkQuotient f x))

/-- The quotient spectrum sits over both `X` and `Spec κ(f(x))` in a commuting
square. -/
theorem fromSpecSourceStalkQuotient_fac {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fromSpecSourceStalkQuotient f x ≫ f =
      fromSpecSourceStalkQuotientToSpecResidueField f x ≫
        S.fromSpecResidueField (f x) := by
  rw [fromSpecSourceStalkQuotient, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk]
  change _ = Spec.map (CommRingCat.ofHom (residueFieldToSourceStalkQuotient f x)) ≫
    Spec.map (S.residue (f x)) ≫ S.fromSpecStalk (f x)
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rfl

/-- The induced morphism from `Spec(𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x})` to the
scheme-theoretic fibre `X_{f(x)}`. -/
noncomputable def fromSpecSourceStalkQuotientToFiber {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    Spec (CommRingCat.of (sourceStalkQuotient f x)) ⟶ f.fiber (f x) :=
  pullback.lift (fromSpecSourceStalkQuotient f x)
    (fromSpecSourceStalkQuotientToSpecResidueField f x)
    (fromSpecSourceStalkQuotient_fac f x)

set_option backward.isDefEq.respectTransparency false in
/-- The closed point of the quotient spectrum is sent to the distinguished
fibre point `f.asFiber x`. -/
theorem fromSpecSourceStalkQuotientToFiber_asFiber {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    fromSpecSourceStalkQuotientToFiber f x
        (closedPoint (CommRingCat.of (sourceStalkQuotient f x))) =
      f.asFiber x := by
  letI : IsLocalHom (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  apply (f.fiberι (f x)).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply]
  change (fromSpecSourceStalkQuotientToFiber f x ≫ pullback.fst _ _) _ = _
  rw [fromSpecSourceStalkQuotientToFiber, pullback.lift_fst]
  change X.fromSpecStalk x
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x)))
      (closedPoint (sourceStalkQuotient f x))) = _
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint, f.fiberι_asFiber]

/-- The structure map `𝒪_{X, x} → 𝒪_{X_{f(x)}, x}` kills the extended
maximal ideal `𝔪_{f(x)} 𝒪_{X, x}`. -/
theorem sourceStalkToFiberStalk_eq_zero_of_mem_map {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (a : X.presheaf.stalk x) (ha : a ∈ sourceStalkBaseMaximalIdeal f x) :
    (sourceStalkToFiberStalk f x).hom a = 0 := by
  have hle : sourceStalkBaseMaximalIdeal f x ≤
      RingHom.ker (sourceStalkToFiberStalk f x).hom := by
    rw [sourceStalkBaseMaximalIdeal, Ideal.map_le_iff_le_comap]
    intro r hr
    change ((f.stalkMap x ≫ sourceStalkToFiberStalk f x).hom r) = 0
    rw [← fiberBaseResidueFieldToStalk_fac]
    change (fiberBaseResidueFieldToStalk f x).hom ((S.residue (f x)).hom r) = 0
    have hz : (S.residue (f x)).hom r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    rw [hz, map_zero]
  exact hle ha

/-- The induced map `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x} → 𝒪_{X_{f(x)}, x}` from
the fibre inclusion on stalks. -/
noncomputable def sourceStalkQuotientToFiberStalk {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    sourceStalkQuotient f x →+* fiberStalkAt f x :=
  Ideal.Quotient.lift (sourceStalkBaseMaximalIdeal f x) (sourceStalkToFiberStalk f x).hom
    (sourceStalkToFiberStalk_eq_zero_of_mem_map f x)

/-- The induced quotient map sends the class of a source-stalk element to its
image under the fibre-inclusion stalk map. -/
theorem sourceStalkQuotientToFiberStalk_mk {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a : X.presheaf.stalk x) :
    sourceStalkQuotientToFiberStalk f x
        (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x) a) =
      (sourceStalkToFiberStalk f x).hom a := rfl

/-- The local homomorphism `𝒪_{X_{f(x)}, x} → 𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}`
induced by the morphism from the quotient spectrum to the fibre. -/
noncomputable def fiberStalkAtToSourceStalkQuotient {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    fiberStalkAt f x ⟶ CommRingCat.of (sourceStalkQuotient f x) :=
  ((f.fiber (f x)).presheaf.stalkCongr
      (Inseparable.of_eq (fromSpecSourceStalkQuotientToFiber_asFiber f x).symm)).hom ≫
    Scheme.stalkClosedPointTo (fromSpecSourceStalkQuotientToFiber f x)

/-- The map to the quotient represents the quotient spectrum's canonical fibre point. -/
theorem SpecMap_fiberStalkAtToSourceStalkQuotient
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec.map (fiberStalkAtToSourceStalkQuotient f x) ≫
        (f.fiber (f x)).fromSpecStalk (f.asFiber x) =
      fromSpecSourceStalkQuotientToFiber f x := by
  simp only [fiberStalkAtToSourceStalkQuotient, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_hom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

/-- Pulling the fibre-inclusion stalk map back to the quotient is the quotient map. -/
theorem sourceStalkToFiberStalk_comp_toQuotient
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    sourceStalkToFiberStalk f x ≫ fiberStalkAtToSourceStalkQuotient f x =
      CommRingCat.ofHom (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x)) := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk x)).1
  rw [Spec.map_comp, Category.assoc, SpecMap_sourceStalkToFiberStalk_fromSpecStalk,
    ← Category.assoc, SpecMap_fiberStalkAtToSourceStalkQuotient]
  change (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst]
  rfl

/-- The two comparison maps between the fibre stalk and the source-stalk
quotient are inverse on the quotient. -/
theorem fiberStalkAtToSourceStalkQuotient_comp_toFiberStalk {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    (fiberStalkAtToSourceStalkQuotient f x).hom.comp
        (sourceStalkQuotientToFiberStalk f x) =
      RingHom.id (sourceStalkQuotient f x) := by
  apply Ideal.Quotient.ringHom_ext
  exact congrArg CommRingCat.Hom.hom (sourceStalkToFiberStalk_comp_toQuotient f x)

/-- The two comparison maps between the fibre stalk and the source-stalk
quotient are inverse on the fibre stalk. -/
theorem sourceStalkQuotientToFiberStalk_comp_toQuotient {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) :
    (sourceStalkQuotientToFiberStalk f x).comp
        (fiberStalkAtToSourceStalkQuotient f x).hom =
      RingHom.id (fiberStalkAt f x) := by
  have h : fiberStalkAtToSourceStalkQuotient f x ≫
      CommRingCat.ofHom (sourceStalkQuotientToFiberStalk f x) = 𝟙 (fiberStalkAt f x) := by
    apply Spec.map_injective
    apply (cancel_mono ((f.fiber (f x)).fromSpecStalk (f.asFiber x))).1
    apply (cancel_mono (f.fiberι (f x))).1
    simp only [Spec.map_comp, Spec.map_id, Category.id_comp, Category.assoc]
    rw [← Category.assoc _ _ (f.fiberι (f x)), SpecMap_fiberStalkAtToSourceStalkQuotient]
    change Spec.map (CommRingCat.ofHom (sourceStalkQuotientToFiberStalk f x)) ≫
      (pullback.lift _ _ _ ≫ pullback.fst _ _) = _
    rw [pullback.lift_fst]
    change Spec.map (CommRingCat.ofHom (sourceStalkQuotientToFiberStalk f x)) ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ X.fromSpecStalk x) = _
    rw [← Spec.map_comp_assoc]
    exact SpecMap_sourceStalkToFiberStalk_fromSpecStalk f x
  exact congrArg CommRingCat.Hom.hom h

/-- The stalk of the scheme-theoretic fibre at the distinguished point is
isomorphic to the quotient of the source stalk by the extended maximal ideal. -/
noncomputable def fiberStalkAtEquivQuotient {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberStalkAt f x ≃+* sourceStalkQuotient f x :=
  RingEquiv.ofRingHom (fiberStalkAtToSourceStalkQuotient f x).hom
    (sourceStalkQuotientToFiberStalk f x)
    (fiberStalkAtToSourceStalkQuotient_comp_toFiberStalk f x)
    (sourceStalkQuotientToFiberStalk_comp_toQuotient f x)

/-- The fibre-stalk quotient isomorphism identifies the fibre-inclusion stalk
map with the quotient map. -/
theorem fiberStalkAtEquivQuotient_symm_mk {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (a : X.presheaf.stalk x) :
    (fiberStalkAtEquivQuotient f x).symm
        (Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x) a) =
      (sourceStalkToFiberStalk f x).hom a := rfl

/-- The quotient `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}` is isomorphic to the
residue-field tensor product `𝒪_{X, x} ⊗_{𝒪_{S, f(x)}} κ(f(x))`. -/
noncomputable def sourceStalkQuotientEquivTensor {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    sourceStalkQuotient f x ≃+* sourceStalkTensorResidueField f x :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x)
      (maximalIdeal (S.presheaf.stalk (f x)))).toRingEquiv

/-- The stalk of the scheme-theoretic fibre at the distinguished point is
isomorphic to the residue-field tensor product of the source stalk. -/
noncomputable def fiberStalkAtEquivTensor {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberStalkAt f x ≃+* sourceStalkTensorResidueField f x :=
  (fiberStalkAtEquivQuotient f x).trans (sourceStalkQuotientEquivTensor f x)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of the fibre is the canonical scalar pushout of the source stalk. -/
theorem fiberStalk_isPushout {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    letI : Algebra (S.presheaf.stalk (f x)) (fiberStalkAt f x) :=
      ((sourceStalkToFiberStalk f x).hom.comp (f.stalkMap x).hom).toAlgebra
    letI : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (fiberStalkAt f x) := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (S.presheaf.stalk (f x)) (S.residueField (f x))
        (fiberStalkAt f x) := IsScalarTower.of_algebraMap_eq' <|
      congrArg CommRingCat.Hom.hom (fiberBaseResidueFieldToStalk_fac f x).symm
    Algebra.IsPushout (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (S.residueField (f x)) (fiberStalkAt f x) := by
  letI : Algebra (S.presheaf.stalk (f x)) (fiberStalkAt f x) :=
    ((sourceStalkToFiberStalk f x).hom.comp (f.stalkMap x).hom).toAlgebra
  letI : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (fiberStalkAt f x) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (S.presheaf.stalk (f x)) (S.residueField (f x))
      (fiberStalkAt f x) := IsScalarTower.of_algebraMap_eq' <|
    congrArg CommRingCat.Hom.hom (fiberBaseResidueFieldToStalk_fac f x).symm
  let e : sourceStalkTensorResidueField f x ≃ₐ[X.presheaf.stalk x] fiberStalkAt f x :=
    @AlgEquiv.ofRingEquiv (X.presheaf.stalk x) (sourceStalkTensorResidueField f x)
      (fiberStalkAt f x) _ _ _ _ _ (fiberStalkAtEquivTensor f x).symm (by
        intro a
        change (fiberStalkAtEquivQuotient f x).symm
          ((sourceStalkQuotientEquivTensor f x).symm
            (a ⊗ₜ[S.presheaf.stalk (f x)] 1)) = _
        have hq : (sourceStalkQuotientEquivTensor f x).symm
            (a ⊗ₜ[S.presheaf.stalk (f x)] 1) =
            Ideal.Quotient.mk (sourceStalkBaseMaximalIdeal f x) a := by
          apply (sourceStalkQuotientEquivTensor f x).injective
          rw [RingEquiv.apply_symm_apply]
          rfl
        rw [hq]
        exact fiberStalkAtEquivQuotient_symm_mk f x a)
  refine ⟨?_⟩
  refine IsBaseChange.of_equiv e.toLinearEquiv ?_
  intro r
  obtain ⟨a, rfl⟩ := S.residue_surjective (f x) r
  change e (1 ⊗ₜ[S.presheaf.stalk (f x)] ((S.residue (f x)).hom a)) =
    (fiberBaseResidueFieldToStalk f x).hom ((S.residue (f x)).hom a)
  have ht : (1 : X.presheaf.stalk x) ⊗ₜ[S.presheaf.stalk (f x)]
      ((S.residue (f x)).hom a) = (f.stalkMap x).hom a ⊗ₜ 1 := by
    have hs : algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x) =
        (f.stalkMap x).hom := rfl
    have hr : algebraMap (S.presheaf.stalk (f x)) (S.residueField (f x)) =
        (S.residue (f x)).hom := rfl
    have h := (Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := S.presheaf.stalk (f x)) (A := X.presheaf.stalk x)
      (B := S.residueField (f x)) a).symm
    rw [hs, hr] at h
    exact h
  rw [ht]
  change e (algebraMap (X.presheaf.stalk x) (sourceStalkTensorResidueField f x)
    ((f.stalkMap x).hom a)) = _
  rw [e.commutes]
  exact congrArg (fun φ : S.presheaf.stalk (f x) ⟶ fiberStalkAt f x => φ a)
    (fiberBaseResidueFieldToStalk_fac f x).symm

end AlgebraicGeometry.Scheme.Hom
