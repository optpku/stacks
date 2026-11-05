/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Field
public import ReasLib.RingTheory.Kaehler.Conormal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.StalkQuotient
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Differentials

/-!
# Cotangent spaces of scheme-theoretic fibres

This file compares the cotangent space of the distinguished point of a
scheme-theoretic fibre with the fibre of the relative Kähler differentials.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The conormal map from the cotangent space of the distinguished fibre
stalk to the Kähler differentials over the residue field of the image point. -/
noncomputable def fiberCotangentToKaehlerLinearMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    let A := fiberStalkAt f x
    let κ := fiberResidueFieldAt f x
    IsLocalRing.CotangentSpace A →ₗ[A] κ ⊗[A] Ω[A⁄S.residueField (f x)] :=
  let A := fiberStalkAt f x
  let κ := fiberResidueFieldAt f x
  let eCot : IsLocalRing.CotangentSpace A ≃ₗ[A]
      (RingHom.ker (algebraMap A κ)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ IsLocalRing.ker_residue.symm
  (KaehlerDifferential.kerCotangentToTensor
    (S.residueField (f x)) A κ).comp eCot.toLinearMap

/-- If the residue field of the distinguished fibre point is separable over
the residue field of the image point, the conormal map is bijective. -/
theorem fiberCotangentToKaehlerLinearMap_bijective_of_isSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (fiberResidueFieldAt f x)) :
    Function.Bijective (fiberCotangentToKaehlerLinearMap f x) := by
  letI := h_sep
  letI : Algebra.FormallyEtale (S.residueField (f x)) (fiberResidueFieldAt f x) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have hsurj : Function.Surjective
      (algebraMap (fiberStalkAt f x) (fiberResidueFieldAt f x)) :=
    (f.fiber (f x)).residue_surjective (f.asFiber x)
  have hconormal := KaehlerDifferential.Conormal.bijective_of_formallyEtale
    (R := S.residueField (f x)) hsurj
  let e := Ideal.Cotangent.equivOfEq
    (IsLocalRing.maximalIdeal (fiberStalkAt f x))
    (RingHom.ker (algebraMap (fiberStalkAt f x) (fiberResidueFieldAt f x)))
    IsLocalRing.ker_residue.symm
  exact hconormal.comp e.bijective

/-- The canonical `κ(x)`-module structure on the cotangent space of the
distinguished fibre stalk, transported across its residue-field equivalence. -/
noncomputable instance fiberCotangentSpaceSourceResidueFieldModule
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Module (X.residueField x)
      (IsLocalRing.CotangentSpace (fiberStalkAt f x)) :=
  -- Local instance justification (defeq pin): expose the generic cotangent-space
  -- module through the definitional identification of the fibre residue field.
  let _ : Module (fiberResidueFieldAt f x)
      (IsLocalRing.CotangentSpace (fiberStalkAt f x)) := by
    change Module (IsLocalRing.ResidueField (fiberStalkAt f x))
      (IsLocalRing.CotangentSpace (fiberStalkAt f x))
    infer_instance
  Module.compHom _ (fiberResidueFieldAlgEquiv f x).symm.toRingHom

/-- The fibre-stalk action on its cotangent space factors through `κ(x)`. -/
instance fiberCotangentSpaceSourceResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (fiberStalkAt f x) (X.residueField x)
      (IsLocalRing.CotangentSpace (fiberStalkAt f x)) := by
  letI : Module (fiberResidueFieldAt f x)
      (IsLocalRing.CotangentSpace (fiberStalkAt f x)) := by
    change Module (IsLocalRing.ResidueField (fiberStalkAt f x))
      (IsLocalRing.CotangentSpace (fiberStalkAt f x))
    infer_instance
  letI : IsScalarTower (fiberStalkAt f x) (fiberResidueFieldAt f x)
      (IsLocalRing.CotangentSpace (fiberStalkAt f x)) := by
    change IsScalarTower (fiberStalkAt f x) (IsLocalRing.ResidueField (fiberStalkAt f x))
      (IsLocalRing.CotangentSpace (fiberStalkAt f x))
    infer_instance
  apply IsScalarTower.of_algebraMap_smul
  intro a v
  change (fiberResidueFieldAlgEquiv f x).symm
    (algebraMap (fiberStalkAt f x) (X.residueField x) a) • v = a • v
  have h : (fiberResidueFieldAlgEquiv f x).symm
      (algebraMap (fiberStalkAt f x) (X.residueField x) a) =
        algebraMap (fiberStalkAt f x) (fiberResidueFieldAt f x) a := by
    apply (fiberResidueFieldAlgEquiv f x).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (congrArg (fun φ : fiberStalkAt f x ⟶ X.residueField x => φ a)
      (fiberStalkToSourceResidueField_factor f x)).symm
  rw [h, IsScalarTower.algebraMap_smul]

/-- Restriction of `κ(x)`-linear forms on the fibre cotangent space along the
fibre stalk is compatible with scalar multiplication. -/
instance fiberCotangentSpaceSourceResidueFieldCompatibleSMul
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    LinearMap.CompatibleSMul
      (IsLocalRing.CotangentSpace (fiberStalkAt f x)) (X.residueField x)
      (fiberStalkAt f x) (X.residueField x) := by
  infer_instance

/-- The canonical comparison from the residue-field fibre of the source-stalk
Kähler differentials to the corresponding fibre-stalk Kähler differentials. -/
noncomputable def sourceKaehlerTensorToFiberLinearMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    X.residueField x ⊗[X.presheaf.stalk x]
        CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[X.residueField x]
      X.residueField x ⊗[fiberStalkAt f x]
        Ω[fiberStalkAt f x⁄S.residueField (f x)] :=
  -- Local instance justification (defeq pin): use the target-to-source stalk map
  -- defining the source Kähler differential.
  let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := stalkAlgebra f x
  -- Local instance justification (defeq pin): use the composite target-to-fibre
  -- stalk map determined by the fixed morphism and distinguished fibre point.
  let _ : Algebra (S.presheaf.stalk (f x)) (fiberStalkAt f x) :=
    ((sourceStalkToFiberStalk f x).hom.comp (f.stalkMap x).hom).toAlgebra
  -- Local instance justification (defeq pin): identify the preceding composite
  -- algebra map with scalar restriction through the source stalk.
  let _ : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (fiberStalkAt f x) := IsScalarTower.of_algebraMap_eq' rfl
  -- Local instance justification (defeq pin): identify the same composite map
  -- with scalar restriction through the base-point residue field.
  let _ : IsScalarTower (S.presheaf.stalk (f x)) (S.residueField (f x))
      (fiberStalkAt f x) :=
    IsScalarTower.of_algebraMap_eq' <|
      congrArg CommRingCat.Hom.hom (fiberBaseResidueFieldToStalk_fac f x).symm
  let widen :
      X.residueField x ⊗[X.presheaf.stalk x]
          CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[X.residueField x]
        X.residueField x ⊗[fiberStalkAt f x]
          (fiberStalkAt f x ⊗[X.presheaf.stalk x]
            CommRingCat.KaehlerDifferential (f.stalkMap x)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (X.presheaf.stalk x) (fiberStalkAt f x) (X.residueField x)
      (X.residueField x) (CommRingCat.KaehlerDifferential (f.stalkMap x))).symm.toLinearMap
  let baseChange :
      fiberStalkAt f x ⊗[X.presheaf.stalk x]
          CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[fiberStalkAt f x]
        Ω[fiberStalkAt f x⁄S.presheaf.stalk (f x)] :=
    KaehlerDifferential.mapBaseChange
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x) (fiberStalkAt f x)
  let changeBase :
      Ω[fiberStalkAt f x⁄S.presheaf.stalk (f x)] →ₗ[fiberStalkAt f x]
        Ω[fiberStalkAt f x⁄S.residueField (f x)] :=
    KaehlerDifferential.map
      (S.presheaf.stalk (f x)) (S.residueField (f x))
      (fiberStalkAt f x) (fiberStalkAt f x)
  let toFiber := changeBase.comp baseChange
  let collapse :
      X.residueField x ⊗[fiberStalkAt f x]
          (fiberStalkAt f x ⊗[X.presheaf.stalk x]
            CommRingCat.KaehlerDifferential (f.stalkMap x)) →ₗ[X.residueField x]
        X.residueField x ⊗[fiberStalkAt f x]
          Ω[fiberStalkAt f x⁄S.residueField (f x)] :=
    TensorProduct.AlgebraTensorModule.lTensor
      (X.residueField x) (X.residueField x) toFiber
  collapse.comp widen

set_option maxHeartbeats 1000000 in
/-- For a separable residue-field extension, the source-to-fibre Kähler
tensor comparison is bijective. -/
theorem sourceKaehlerTensorToFiberLinearMap_bijective_of_isSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x)) :
    Function.Bijective (sourceKaehlerTensorToFiberLinearMap f x) := by
  -- Local instance justification (defeq pin): use the target-to-source stalk map
  -- defining the source Kähler differential.
  let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := stalkAlgebra f x
  -- Local instance justification (defeq pin): use the composite target-to-fibre
  -- stalk map determined by the fixed morphism and distinguished fibre point.
  let _ : Algebra (S.presheaf.stalk (f x)) (fiberStalkAt f x) :=
    ((sourceStalkToFiberStalk f x).hom.comp (f.stalkMap x).hom).toAlgebra
  -- Local instance justification (defeq pin): identify the preceding composite
  -- algebra map with scalar restriction through the source stalk.
  let _ : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (fiberStalkAt f x) := IsScalarTower.of_algebraMap_eq' rfl
  -- Local instance justification (defeq pin): identify the same composite map
  -- with scalar restriction through the base-point residue field.
  let _ : IsScalarTower (S.presheaf.stalk (f x)) (S.residueField (f x))
      (fiberStalkAt f x) :=
    IsScalarTower.of_algebraMap_eq' <|
      congrArg CommRingCat.Hom.hom (fiberBaseResidueFieldToStalk_fac f x).symm
  letI : Algebra.IsPushout (S.presheaf.stalk (f x)) (S.residueField (f x))
      (X.presheaf.stalk x) (fiberStalkAt f x) := (fiberStalk_isPushout f x).symm
  let e := KaehlerDifferential.tensorKaehlerEquiv
    (S.presheaf.stalk (f x)) (S.residueField (f x))
    (X.presheaf.stalk x) (fiberStalkAt f x)
  have heq : (KaehlerDifferential.map (S.presheaf.stalk (f x)) (S.residueField (f x))
      (fiberStalkAt f x) (fiberStalkAt f x)).comp
        (KaehlerDifferential.mapBaseChange (S.presheaf.stalk (f x))
          (X.presheaf.stalk x) (fiberStalkAt f x)) = e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    obtain ⟨m, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x) m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add m n hm hn => simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hm hn
    | tmul r s =>
      simp only [Derivation.tensorProductTo_tmul, TensorProduct.tmul_smul,
        LinearMap.comp_apply, LinearMap.map_smul_of_tower,
        KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
        e, LinearEquiv.coe_coe, KaehlerDifferential.tensorKaehlerEquiv_tmul_D,
        map_smul, Algebra.algebraMap_self, RingHom.id_apply]
  change Function.Bijective
    ((TensorProduct.AlgebraTensorModule.lTensor (X.residueField x) (X.residueField x)
      ((KaehlerDifferential.map (S.presheaf.stalk (f x)) (S.residueField (f x))
        (fiberStalkAt f x) (fiberStalkAt f x)).comp
          (KaehlerDifferential.mapBaseChange (S.presheaf.stalk (f x))
            (X.presheaf.stalk x) (fiberStalkAt f x)))).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (X.presheaf.stalk x)
        (fiberStalkAt f x) (X.residueField x) (X.residueField x)
        (CommRingCat.KaehlerDifferential (f.stalkMap x))).symm.toLinearMap)
  rw [heq]
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.residueField x) (X.residueField x)) e).bijective.comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (X.presheaf.stalk x)
        (fiberStalkAt f x) (X.residueField x) (X.residueField x)
        (CommRingCat.KaehlerDifferential (f.stalkMap x))).symm.bijective

/-- The fibre-stalk conormal map followed by transport of the fibre residue
field tensor factor to `κ(x)`. -/
noncomputable def fiberCotangentToKaehlerResidueTensorLinearMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    let A := fiberStalkAt f x
    IsLocalRing.CotangentSpace A →ₗ[A]
      X.residueField x ⊗[A] Ω[A⁄S.residueField (f x)] :=
  let A := fiberStalkAt f x
  let tensorMap :
      fiberResidueFieldAt f x ⊗[A] Ω[A⁄S.residueField (f x)] →ₗ[A]
        X.residueField x ⊗[A] Ω[A⁄S.residueField (f x)] :=
    TensorProduct.map (fiberResidueFieldToSourceResidueFieldLinearMap f x)
      (LinearMap.id : Ω[A⁄S.residueField (f x)] →ₗ[A]
        Ω[A⁄S.residueField (f x)])
  tensorMap.comp (fiberCotangentToKaehlerLinearMap f x)

/-- Under separability, transport of the residue-field tensor factor preserves
bijectivity of the fibre-stalk conormal map. -/
theorem fiberCotangentToKaehlerResidueTensorLinearMap_bijective_of_isSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (fiberResidueFieldAt f x)) :
    Function.Bijective
      (fiberCotangentToKaehlerResidueTensorLinearMap f x) := by
  let e : fiberResidueFieldAt f x ≃ₐ[fiberStalkAt f x] X.residueField x :=
    @AlgEquiv.ofRingEquiv (fiberStalkAt f x) (fiberResidueFieldAt f x)
      (X.residueField x) _ _ _ _ _ (fiberResidueFieldAlgEquiv f x).toRingEquiv (by
      intro a
      exact congrArg (fun φ : fiberStalkAt f x ⟶ X.residueField x => φ a)
        (fiberStalkToSourceResidueField_factor f x))
  have he := (TensorProduct.congr e.toLinearEquiv
    (LinearEquiv.refl (fiberStalkAt f x)
      Ω[fiberStalkAt f x⁄S.residueField (f x)])).bijective
  exact he.comp (fiberCotangentToKaehlerLinearMap_bijective_of_isSeparable f x h_sep)

namespace FiberCotangent

/-- The transported fibre-stalk conormal map, extended to a `κ(x)`-linear
map by surjectivity of the fibre-stalk residue map. -/
noncomputable def kaehlerComparison
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsLocalRing.CotangentSpace (fiberStalkAt f x) →ₗ[X.residueField x]
      X.residueField x ⊗[fiberStalkAt f x]
        Ω[fiberStalkAt f x⁄S.residueField (f x)] :=
  LinearMap.extendScalarsOfSurjective
    (fiberStalkToSourceResidueField_surjective f x)
    (fiberCotangentToKaehlerResidueTensorLinearMap f x)

/-- Under separability, the `κ(x)`-linear fibre-stalk conormal comparison is
bijective. -/
theorem kaehlerComparison_bijective_of_isSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x)) :
    Function.Bijective (kaehlerComparison f x) := by
  letI := h_sep
  have h_sep' : Algebra.IsSeparable
      (S.residueField (f x)) (fiberResidueFieldAt f x) :=
    AlgEquiv.Algebra.isSeparable (fiberResidueFieldAlgEquiv f x).symm
  exact fiberCotangentToKaehlerResidueTensorLinearMap_bijective_of_isSeparable f x h_sep'

end FiberCotangent

/-- For a separable residue-field extension, the fibre cotangent space is
canonically equivalent over `κ(x)` to the transported fibre Kähler tensor. -/
noncomputable def fiberCotangentToKaehlerEquivOfIsSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x)) :
    IsLocalRing.CotangentSpace (fiberStalkAt f x) ≃ₗ[X.residueField x]
      X.residueField x ⊗[fiberStalkAt f x]
        Ω[fiberStalkAt f x⁄S.residueField (f x)] :=
  LinearEquiv.ofBijective
    (FiberCotangent.kaehlerComparison f x)
    (FiberCotangent.kaehlerComparison_bijective_of_isSeparable f x h_sep)

/-- The fibre cotangent equivalence evaluates to the extended conormal map. -/
theorem fiberCotangentToKaehlerEquivOfIsSeparable_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x))
    (v : IsLocalRing.CotangentSpace (fiberStalkAt f x)) :
    fiberCotangentToKaehlerEquivOfIsSeparable f x h_sep v =
      FiberCotangent.kaehlerComparison f x v := rfl

/-- If `κ(x)` is separable over `κ(f(x))`, the cotangent space of the
distinguished fibre stalk is canonically equivalent to the residue-field
fibre of the relative Kähler differentials at `x`. -/
noncomputable def cotangentSpaceToKaehlerTensorEquivOfIsSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x)) :
    IsLocalRing.CotangentSpace (fiberStalkAt f x) ≃ₗ[X.residueField x]
      X.residueField x ⊗[X.presheaf.stalk x]
        CommRingCat.KaehlerDifferential (f.stalkMap x) :=
  (fiberCotangentToKaehlerEquivOfIsSeparable f x h_sep).trans <|
    (LinearEquiv.ofBijective (sourceKaehlerTensorToFiberLinearMap f x)
      (sourceKaehlerTensorToFiberLinearMap_bijective_of_isSeparable
        f x h_sep)).symm

/-- The separable cotangent/Kähler equivalence applies the inverse of the
source-to-fibre Kähler comparison after the fibre conormal equivalence. -/
theorem cotangentSpaceToKaehlerTensorEquivOfIsSeparable_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x))
    (v : IsLocalRing.CotangentSpace (fiberStalkAt f x)) :
    cotangentSpaceToKaehlerTensorEquivOfIsSeparable f x h_sep v =
      ((LinearEquiv.ofBijective (sourceKaehlerTensorToFiberLinearMap f x)
        (sourceKaehlerTensorToFiberLinearMap_bijective_of_isSeparable
          f x h_sep)).symm)
        (fiberCotangentToKaehlerEquivOfIsSeparable f x h_sep v) := rfl

/-- If the canonical map `κ(f(x)) → κ(x)` is bijective, the cotangent space
of the distinguished fibre stalk is canonically equivalent to the fibre of
the relative Kähler differentials at `x`. -/
noncomputable def cotangentSpaceToKaehlerTensorEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom) :
    IsLocalRing.CotangentSpace (fiberStalkAt f x) ≃ₗ[X.residueField x]
      X.residueField x ⊗[X.presheaf.stalk x]
        CommRingCat.KaehlerDifferential (f.stalkMap x) :=
  cotangentSpaceToKaehlerTensorEquivOfIsSeparable f x <|
    AlgEquiv.Algebra.isSeparable (residueFieldAlgEquivOfBijective f x h)

/-- The cotangent/Kähler equivalence for a bijective residue-field map is the
corresponding separable-extension equivalence. -/
theorem cotangentSpaceToKaehlerTensorEquiv_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom)
    (v : IsLocalRing.CotangentSpace (fiberStalkAt f x)) :
    cotangentSpaceToKaehlerTensorEquiv f x h v =
      cotangentSpaceToKaehlerTensorEquivOfIsSeparable f x
        (AlgEquiv.Algebra.isSeparable (residueFieldAlgEquivOfBijective f x h)) v := rfl

/-- For a separable residue-field extension, the relative tangent space is
canonically the `κ(x)`-linear dual of the fibre cotangent space. -/
noncomputable def relativeTangentSpaceLinearDualOfIsSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x)) :
    tangentSpaceAt f x ≃ₗ[X.residueField x]
      (IsLocalRing.CotangentSpace (fiberStalkAt f x) →ₗ[X.residueField x]
        X.residueField x) :=
  (relativeTangentSpaceLinearDual f x).trans <|
    (LinearMap.ringLmapEquivSelf
      (X.residueField x) (X.residueField x)
      (CommRingCat.KaehlerDifferential (f.stalkMap x) →ₗ[X.presheaf.stalk x]
        X.residueField x)).symm |>.trans <|
      (TensorProduct.AlgebraTensorModule.lift.equiv
        (X.presheaf.stalk x) (X.residueField x) (X.residueField x)
        (X.residueField x) (CommRingCat.KaehlerDifferential (f.stalkMap x))
        (X.residueField x)).trans <|
        ((cotangentSpaceToKaehlerTensorEquivOfIsSeparable f x h_sep).arrowCongr
          (LinearEquiv.refl (X.residueField x) (X.residueField x))).symm

/-- If the canonical residue-field map is bijective, the relative tangent
space is canonically the `κ(x)`-linear dual of the fibre cotangent space. -/
noncomputable def relativeTangentSpaceToCotangentLinearDual
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom) :
    tangentSpaceAt f x ≃ₗ[X.residueField x]
      (IsLocalRing.CotangentSpace (fiberStalkAt f x) →ₗ[X.residueField x]
        X.residueField x) :=
  relativeTangentSpaceLinearDualOfIsSeparable f x <|
    AlgEquiv.Algebra.isSeparable (residueFieldAlgEquivOfBijective f x h)

end AlgebraicGeometry.Scheme.Hom
