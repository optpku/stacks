/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Kummer.Isomorphisms
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry RingedSpace
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kummer

/-- An invertible module equipped with a trivialization of its nth tensor power. -/
structure Pair (S : Scheme.{u}) (n : ℕ) where
  /-- The underlying invertible module. -/
  lineBundle : S.Modules
  /-- Tensor-invertibility of the underlying module. -/
  invertible_lineBundle : Invertible lineBundle
  /-- The chosen tensor-power trivialization. -/
  trivialization : TensorPower.sheaf lineBundle n ≅ SheafOfModules.unit S.ringCatSheaf

/-- Construct an equipped pair from its module and tensor-power trivialization. -/
def Pair.ofData {S : Scheme.{u}} {n : ℕ} (lineBundle : S.Modules)
    (invertible_lineBundle : Invertible lineBundle)
    (trivialization : TensorPower.sheaf lineBundle n ≅ SheafOfModules.unit S.ringCatSheaf) :
    Pair S n :=
  ⟨lineBundle, invertible_lineBundle, trivialization⟩

/-- The constructor retains both the module and its specified tensor-power trivialization. -/
theorem Pair.ofData_spec {S : Scheme.{u}} {n : ℕ} (lineBundle : S.Modules)
    (invertible_lineBundle : Invertible lineBundle)
    (trivialization : TensorPower.sheaf lineBundle n ≅ SheafOfModules.unit S.ringCatSheaf) :
    (Pair.ofData lineBundle invertible_lineBundle trivialization).lineBundle = lineBundle ∧
      (Pair.ofData lineBundle invertible_lineBundle trivialization).trivialization =
        trivialization := sorry

/-- An isomorphism of equipped pairs preserves their chosen power trivializations. -/
structure PairIso {S : Scheme.{u}} {n : ℕ} (P Q : Pair S n) where
  /-- The underlying module isomorphism. -/
  hom : P.lineBundle ≅ Q.lineBundle
  /-- Compatibility with the tensor-power trivializations. -/
  preserves_trivialization : hom ∈ isomorphisms n P.trivialization Q.trivialization

/-- Construct an equipped-pair isomorphism from a compatible module isomorphism. -/
def PairIso.ofHom {S : Scheme.{u}} {n : ℕ} {P Q : Pair S n}
    (hom : P.lineBundle ≅ Q.lineBundle)
    (preserves_trivialization : hom ∈ isomorphisms n P.trivialization Q.trivialization) :
    PairIso P Q :=
  ⟨hom, preserves_trivialization⟩

/-- The isomorphism constructor retains its map and the power-compatibility equation. -/
theorem PairIso.ofHom_spec {S : Scheme.{u}} {n : ℕ} {P Q : Pair S n}
    (hom : P.lineBundle ≅ Q.lineBundle)
    (preserves_trivialization : hom ∈ isomorphisms n P.trivialization Q.trivialization) :
    (PairIso.ofHom hom preserves_trivialization).hom = hom ∧
      TensorPower.map (PairIso.ofHom hom preserves_trivialization).hom.hom n ≫
        Q.trivialization.hom = P.trivialization.hom := sorry

/-- Identity module isomorphisms preserve power trivializations. -/
theorem PairIso.refl_compatible {S : Scheme.{u}} {n : ℕ} (P : Pair S n) :
    Iso.refl P.lineBundle ∈ isomorphisms n P.trivialization P.trivialization := sorry

/-- Inversion preserves compatibility with power trivializations. -/
theorem PairIso.symm_compatible {S : Scheme.{u}} {n : ℕ} {P Q : Pair S n}
    (e : PairIso P Q) :
    e.hom.symm ∈ isomorphisms n Q.trivialization P.trivialization := sorry

/-- Composition preserves compatibility with power trivializations. -/
theorem PairIso.trans_compatible {S : Scheme.{u}} {n : ℕ} {P Q R : Pair S n}
    (e : PairIso P Q) (f : PairIso Q R) :
    e.hom ≪≫ f.hom ∈ isomorphisms n P.trivialization R.trivialization := sorry

/-- The identity isomorphism of an equipped pair. -/
def PairIso.refl {S : Scheme.{u}} {n : ℕ} (P : Pair S n) : PairIso P P :=
  ofHom (Iso.refl P.lineBundle) (refl_compatible P)

/-- Invert an equipped-pair isomorphism. -/
def PairIso.symm {S : Scheme.{u}} {n : ℕ} {P Q : Pair S n}
    (e : PairIso P Q) : PairIso Q P :=
  ofHom e.hom.symm (symm_compatible e)

/-- Compose equipped-pair isomorphisms. -/
def PairIso.trans {S : Scheme.{u}} {n : ℕ} {P Q R : Pair S n}
    (e : PairIso P Q) (f : PairIso Q R) : PairIso P R :=
  ofHom (e.hom ≪≫ f.hom) (trans_compatible e f)

/-- Equipped pairs are equivalent precisely when a compatible isomorphism exists. -/
def pairSetoid (S : Scheme.{u}) (n : ℕ) : Setoid (Pair S n) where
  r P Q := Nonempty (PairIso P Q)
  iseqv := ⟨fun P ↦ ⟨PairIso.refl P⟩,
    fun h ↦ h.elim (fun e ↦ ⟨e.symm⟩),
    fun h k ↦ h.elim (fun e ↦ k.elim (fun f ↦ ⟨e.trans f⟩))⟩

/-- The trivial equipped pair has structure module and the structural power trivialization. -/
def Pair.unit (S : Scheme.{u}) (n : ℕ) : Pair S n :=
  let rec unitPowerIso : (k : ℕ) →
      TensorPower.sheaf (SheafOfModules.unit S.ringCatSheaf) k ≅
        (SheafOfModules.unit S.ringCatSheaf : S.Modules)
    | 0 => Iso.refl _
    | k + 1 => (Iso.refl _ ⊗ᵢ unitPowerIso k) ≪≫
        (unitIsoTensorUnit S.toRingedSpace ⊗ᵢ Iso.refl _) ≪≫ λ_ _
  ofData (SheafOfModules.unit S.ringCatSheaf) Invertible.unit_invertible (unitPowerIso n)

/-- Tensor equipped pairs using the tensor product of their chosen trivializations. -/
def Pair.tensor {S : Scheme.{u}} {n : ℕ} (P Q : Pair S n) : Pair S n :=
  let interchange (A B C D : S.Modules) :
      (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
    α_ A B (C ⊗ D) ≪≫ (Iso.refl A ⊗ᵢ (α_ B C D).symm) ≪≫
      (Iso.refl A ⊗ᵢ (β_ B C ⊗ᵢ Iso.refl D)) ≪≫
      (Iso.refl A ⊗ᵢ α_ C B D) ≪≫ (α_ A C (B ⊗ D)).symm
  let rec tensorPowerTensorIso (k : ℕ) :
      TensorPower.sheaf (P.lineBundle ⊗ Q.lineBundle) k ≅
        TensorPower.sheaf P.lineBundle k ⊗ TensorPower.sheaf Q.lineBundle k :=
    match k with
    | 0 => (λ_ _).symm ≪≫ ((unitIsoTensorUnit S.toRingedSpace).symm ⊗ᵢ Iso.refl _)
    | k + 1 => (Iso.refl _ ⊗ᵢ tensorPowerTensorIso k) ≪≫
        interchange P.lineBundle Q.lineBundle
          (TensorPower.sheaf P.lineBundle k) (TensorPower.sheaf Q.lineBundle k)
  ofData (P.lineBundle ⊗ Q.lineBundle)
    (ObjectProperty.prop_tensor P.invertible_lineBundle Q.invertible_lineBundle)
    (tensorPowerTensorIso n ≪≫
      (P.trivialization ⊗ᵢ Q.trivialization) ≪≫
      (unitIsoTensorUnit S.toRingedSpace ⊗ᵢ Iso.refl _) ≪≫ λ_ _)

/-- The dual pair uses the chosen tensor inverse and the dual power trivialization. -/
def Pair.dual {S : Scheme.{u}} {n : ℕ} (P : Pair S n) : Pair S n :=
  let dualOfData (L : S.Modules) [hL : Invertible L]
      (α : TensorPower.sheaf L n ≅ SheafOfModules.unit S.ringCatSheaf) : Pair S n :=
    let rec dualPowerPairing (k : ℕ) : ExactPairing (TensorPower.sheaf L k)
        (TensorPower.sheaf (isInvertibleObject.inverse L) k) :=
      match k with
      | 0 => exactPairingCongr (unitIsoTensorUnit S.toRingedSpace)
          (unitIsoTensorUnit S.toRingedSpace)
      | k + 1 => @exactPairingCongrRight S.Modules _ _
          (L ⊗ TensorPower.sheaf L k)
          (isInvertibleObject.inverse L ⊗ TensorPower.sheaf (isInvertibleObject.inverse L) k)
          (TensorPower.sheaf (isInvertibleObject.inverse L) k ⊗ isInvertibleObject.inverse L)
          (@ExactPairing.tensor S.Modules _ _ L (TensorPower.sheaf L k)
            (isInvertibleObject.inverse L) (TensorPower.sheaf (isInvertibleObject.inverse L) k)
            (isInvertibleObject.exactPairing L) (dualPowerPairing k)) (β_ _ _)
    ofData (isInvertibleObject.inverse L) (isInvertibleObject.inverseIsInvertible L)
      (rightDualIso (dualPowerPairing n)
        (exactPairingCongrLeft (α ≪≫ unitIsoTensorUnit S.toRingedSpace)) ≪≫
          (unitIsoTensorUnit S.toRingedSpace).symm)
  dualOfData P.lineBundle (hL := P.invertible_lineBundle) P.trivialization

/-- Tensor products of compatible-isomorphic equipped pairs are compatible-isomorphic. -/
theorem Pair.tensor_respects_iso {S : Scheme.{u}} {n : ℕ} {P P' Q Q' : Pair S n}
    (e : PairIso P P') (f : PairIso Q Q') :
    Nonempty (PairIso (P.tensor Q) (P'.tensor Q')) := sorry

/-- Dualization preserves compatible isomorphism of equipped pairs. -/
theorem Pair.dual_respects_iso {S : Scheme.{u}} {n : ℕ} {P Q : Pair S n}
    (e : PairIso P Q) : Nonempty (PairIso P.dual Q.dual) := sorry

end AlgebraicGeometry.Scheme.Modules.Kummer
