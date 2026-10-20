/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Indiscrete
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap91.Lemma_91_8_1
public import stacks_project.Chap93.Lemma_93_9_3_Trivial

/-!
# Ext/Hom/Der comparison maps for `Inf(Def_X)` and `T Def_X`

The identifications
`Inf(Def_X) ≃ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ≃ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ≃ Der_k(𝒪_X, 𝒪_X)`
and `T Def_X ≃ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` are realized by named comparison maps
assembled from Lemma 91.8.1, Lemma 37.13.3, and Lemma 29.32.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber
open AlgebraicGeometry.Scheme.Thickening
open AlgebraicGeometry.Scheme.Thickening.FlatLift
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening (moduleQ)
open AlgebraicGeometry.RingedSpace.Module.Associated
open SheafOfModules.Indiscrete
open ArtinianLocalAlgCat
open TrivSqZeroExt
open scoped AlgebraicGeometry DerivedExt DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- The closed immersion `Spec k ⟶ Spec k[ε]`. -/
abbrev dualNumberThickening :
    Spec (CommRingCat.of (residue Λ k).carrier) ⟶
      Spec (CommRingCat.of (dualNumber Λ k).carrier) :=
  specMap (dualNumberToResidue Λ k)

/-- `dualNumberThickening` is the spectrum of the coefficient projection `k[ε] ⟶ k`. -/
theorem dualNumberThickening_eq :
    dualNumberThickening Λ k = specMap (dualNumberToResidue Λ k) := sorry

/-- The dual-number closed immersion is a first-order thickening. -/
instance instIsFirstOrderThickening_dualNumberToResidue :
    IsFirstOrderThickening (specMap (dualNumberToResidue Λ k)) := sorry

/-- The trivial dual-number lift of `hX` as a flat first-order thickening lift. -/
def trivialFlatLift (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    FlatLift (specMap (dualNumberToResidue Λ k)) hX :=
  FlatLift.of (trivialSchemeOver Λ k X hX) (trivialSchemeImmersion Λ k X hX) sorry

/-- `trivialFlatLift` has ambient scheme `trivialScheme`. -/
theorem trivialFlatLift_space (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (trivialFlatLift Λ k X hX).space = trivialScheme Λ k X hX := sorry

/-- The kernel of the coefficient projection `k[ε] ⟶ k`, as a `k`-module. -/
abbrev dualNumberKernel :=
  LinearMap.ker (AlgHom.toLinearMap (fstHom k k k))

/-- An element of `ker(k[ε] → k)` is a dual number with vanishing scalar coefficient. -/
theorem mem_dualNumberKernel_iff (x : DualNumber k) :
    x ∈ dualNumberKernel k ↔ x.fst = 0 := sorry

/-- `a·ε` lies in `ker(k[ε] → k)`. -/
theorem inr_mem_dualNumberKernel (a : k) :
    inr a ∈ dualNumberKernel k := sorry

/-- ε-coefficient identification `ker(k[ε] → k) ≃ k`, sending `a·ε` to `a`. -/
def dualNumberKernelEquiv : dualNumberKernel k ≃ₗ[k] k where
  toFun x := snd (x : DualNumber k)
  invFun a := ⟨inr a, inr_mem_dualNumberKernel k a⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- `dualNumberKernelEquiv` is the second projection on a kernel element. -/
theorem dualNumberKernelEquiv_apply (x : dualNumberKernel k) :
    dualNumberKernelEquiv k x = snd (x : DualNumber k) := sorry

/-- The inverse of `dualNumberKernelEquiv` sends `a` to `a·ε`. -/
theorem dualNumberKernelEquiv_symm_apply (a : k) :
    ((dualNumberKernelEquiv k).symm a : DualNumber k) = inr a := sorry

/-- Associated sheaf of `ker(k[ε] → k)` along a morphism to `Spec k`. -/
def associatedDualNumberKernel (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    X.toRingedSpace.Modules :=
  obj (Scheme.Hom.globalSectionsMap hX) (ModuleCat.of k (dualNumberKernel k))

/-- Unfolding of `associatedDualNumberKernel`. -/
theorem associatedDualNumberKernel_eq (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    associatedDualNumberKernel Λ k X hX =
      obj (Scheme.Hom.globalSectionsMap hX) (ModuleCat.of k (dualNumberKernel k)) := sorry

/-- Canonical isomorphism `Associated(ker(k[ε] → k)) ≅ 𝒪_X` via ε-coefficients. -/
def associatedKernelIsoUnit (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    associatedDualNumberKernel Λ k X hX ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (functor (Scheme.Hom.globalSectionsMap hX)).mapIso
      (LinearEquiv.toModuleIso (dualNumberKernelEquiv k)) ≪≫
    (functor (Scheme.Hom.globalSectionsMap hX)).mapIso (Iso.refl _) ≪≫
    (unitIso (Scheme.Hom.globalSectionsMap hX)).symm ≪≫
    (unitIsoTensorUnit X.toRingedSpace).symm

/-- The forward map of `associatedKernelIsoUnit` is associated-sheaf transport of
`dualNumberKernelEquiv`. -/
theorem associatedKernelIsoUnit_hom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    (associatedKernelIsoUnit Λ k X hX).hom =
      ((functor (Scheme.Hom.globalSectionsMap hX)).mapIso
          (LinearEquiv.toModuleIso (dualNumberKernelEquiv k)) ≪≫
        (unitIso (Scheme.Hom.globalSectionsMap hX)).symm ≪≫
        (unitIsoTensorUnit X.toRingedSpace).symm).hom := sorry

/-- The inverse map of `associatedKernelIsoUnit` is associated-sheaf transport of
`dualNumberKernelEquiv.symm`. -/
theorem associatedKernelIsoUnit_inv (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    (associatedKernelIsoUnit Λ k X hX).inv =
      ((functor (Scheme.Hom.globalSectionsMap hX)).mapIso
          (LinearEquiv.toModuleIso (dualNumberKernelEquiv k)) ≪≫
        (unitIso (Scheme.Hom.globalSectionsMap hX)).symm ≪≫
        (unitIsoTensorUnit X.toRingedSpace).symm).inv := sorry

/-- Associated sheaf of `ker(k[ε] → k)` on `Spec k`. -/
abbrev residueAssociatedKernel :
    (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.Modules :=
  associatedDualNumberKernel Λ k
    (Spec (CommRingCat.of (residue Λ k).carrier)) (𝟙 _)

/-- ε-coefficient isomorphism `Associated(ker) ≅ 𝒪_{Spec k}`. -/
def residueAssociatedIsoUnit :
    residueAssociatedKernel Λ k ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf :=
  associatedKernelIsoUnit Λ k
    (Spec (CommRingCat.of (residue Λ k).carrier)) (𝟙 _)

/-- The dual-number closed immersion, as a morphism of ringed spaces. -/
abbrev residueThickeningRS :
    (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace ⟶
      (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace :=
  (specMap (dualNumberToResidue Λ k)).toShHom

/-- `Spec k` is a one-point space, hence indiscrete. -/
instance instIndiscreteTopology_residueSpec :
    IndiscreteTopology
      (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.carrier := sorry

/-- `Spec k[ε]` is a one-point space, hence indiscrete. -/
instance instIndiscreteTopology_dualNumberSpec :
    IndiscreteTopology
      (Spec (CommRingCat.of (dualNumber Λ k).carrier)).toRingedSpace.carrier := sorry

/-- Top-open ε-coefficient map on `Ker(𝒪_{Spec k[ε]} → i_* 𝒪_{Spec k})`, sending `a·ε` to `a`. -/
def residueKernelSheafToPushforwardTop :
    (kernelIdealSheaf (residueThickeningRS Λ k)).val.obj (Opposite.op ⊤) ⟶
      (((residueThickeningRS Λ k) _*).obj
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)).val.obj
        (Opposite.op ⊤) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun x ↦
          (Scheme.ΓSpecIso (CommRingCat.of (residue Λ k).carrier)).inv
            (snd
              ((Scheme.ΓSpecIso (CommRingCat.of (dualNumber Λ k).carrier)).hom
                (SheafOfModules.RingedSite.KernelIdeal.ιApp
                  (commRingSheafPushforwardMap (residueThickeningRS Λ k))
                  (Opposite.op ⊤) x))))
        sorry))
    sorry

/-- Top-open inverse ε-coefficient map, sending `a` to `a·ε`. -/
def residuePushforwardToKernelSheafTop :
    (((residueThickeningRS Λ k) _*).obj
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)).val.obj
        (Opposite.op ⊤) ⟶
      (kernelIdealSheaf (residueThickeningRS Λ k)).val.obj (Opposite.op ⊤) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun a ↦
          (SheafOfModules.RingedSite.KernelIdeal.sectionsIso
              (commRingSheafPushforwardMap (residueThickeningRS Λ k))
              (Opposite.op ⊤)).inv
            (⟨(Scheme.ΓSpecIso (CommRingCat.of (dualNumber Λ k).carrier)).inv
                (inr ((Scheme.ΓSpecIso (CommRingCat.of (residue Λ k).carrier)).hom a)),
              sorry⟩ :
              SheafOfModules.RingedSite.KernelIdeal.sectionIdeal
                (commRingSheafPushforwardMap (residueThickeningRS Λ k))
                (Opposite.op ⊤)))
        sorry))
    sorry

/-- Top-open identification of the dual-number kernel sheaf with `i_* 𝒪_{Spec k}`. -/
def residueKernelSheafTopIso :
    (kernelIdealSheaf (residueThickeningRS Λ k)).val.obj (Opposite.op ⊤) ≅
      (((residueThickeningRS Λ k) _*).obj
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)).val.obj
        (Opposite.op ⊤) where
  hom := residueKernelSheafToPushforwardTop Λ k
  inv := residuePushforwardToKernelSheafTop Λ k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- ε-coefficient isomorphism `Ker(𝒪_{Spec k[ε]} → i_* 𝒪_k) ≅ i_* 𝒪_{Spec k}`. -/
def residueKernelSheafIsoPushforward :
    kernelIdealSheaf (residueThickeningRS Λ k) ≅
      ((residueThickeningRS Λ k) _*).obj
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf) :=
  isoOfTop
    (kernelIdealSheaf (residueThickeningRS Λ k))
    (((residueThickeningRS Λ k) _*).obj
      (SheafOfModules.unit
        (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf))
    (residueKernelSheafTopIso Λ k)

/-- Top-open ε-coefficient map `Ker(k[ε] → k) ⟶ 𝒪_{Spec k}` on `Spec k`. -/
def residueKernelToUnitTop :
    (idealModule (residueThickeningRS Λ k)).val.obj (Opposite.op ⊤) ⟶
      (SheafOfModules.unit
        (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf).val.obj
        (Opposite.op ⊤) :=
  (((residueThickeningRS Λ k) ^*).map (residueKernelSheafIsoPushforward Λ k).hom ≫
      (pullbackPushforwardAdjunction (residueThickeningRS Λ k)).counit.app
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)).val.app
    (Opposite.op ⊤)

/-- The counit `i^* i_* 𝒪_{Spec k} ⟶ 𝒪_{Spec k}` is an isomorphism on the one-point space. -/
instance instIsIso_counit_app_residueUnit :
    IsIso
      ((pullbackPushforwardAdjunction (residueThickeningRS Λ k)).counit.app
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)) :=
  sorry

/-- Top-open inverse ε-coefficient map `𝒪_{Spec k} ⟶ Ker(k[ε] → k)` on `Spec k`. -/
def residueUnitToKernelTop :
    (SheafOfModules.unit
        (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf).val.obj
        (Opposite.op ⊤) ⟶
      (idealModule (residueThickeningRS Λ k)).val.obj (Opposite.op ⊤) :=
  ((asIso
        ((pullbackPushforwardAdjunction (residueThickeningRS Λ k)).counit.app
          (SheafOfModules.unit
            (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf))).inv ≫
      ((residueThickeningRS Λ k) ^*).map (residueKernelSheafIsoPushforward Λ k).inv).val.app
    (Opposite.op ⊤)

/-- Top-open identification `Ker(k[ε] → k) ≅ k` as modules over `𝒪_{Spec k}(⊤)`. -/
def residueIdealTopIso :
    (idealModule (residueThickeningRS Λ k)).val.obj (Opposite.op ⊤) ≅
      (SheafOfModules.unit
        (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf).val.obj
        (Opposite.op ⊤) where
  hom := residueKernelToUnitTop Λ k
  inv := residueUnitToKernelTop Λ k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- ε-coefficient isomorphism `Ker(Spec k → Spec k[ε]) ≅ 𝒪_{Spec k}`, reconstructed from
the top-open maps `a·ε ↦ a` and `a ↦ a·ε`. -/
def residueKernelIsoUnit :
    idealModule (residueThickeningRS Λ k) ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf :=
  isoOfTop
    (idealModule (residueThickeningRS Λ k))
    (SheafOfModules.unit
      (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)
    (residueIdealTopIso Λ k)

/-- The forward map of `residueKernelIsoUnit` is the sheafification of second projection. -/
theorem residueKernelIsoUnit_hom :
    (residueKernelIsoUnit Λ k).hom =
      homOfTop
        (idealModule (residueThickeningRS Λ k))
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)
        (residueKernelToUnitTop Λ k) := sorry

/-- The inverse map of `residueKernelIsoUnit` is the sheafification of `a ↦ a·ε`. -/
theorem residueKernelIsoUnit_inv :
    (residueKernelIsoUnit Λ k).inv =
      homOfTop
        (SheafOfModules.unit
          (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace.ringCatSheaf)
        (idealModule (residueThickeningRS Λ k))
        (residueUnitToKernelTop Λ k) := sorry

/-- Identification `f^* 𝒞_{Spec k / Spec k[ε]} ≅ 𝒪_X` for the trivial dual-number
thickening, via the ε-coefficient isomorphism `ker(k[ε] → k) ≅ k`. -/
def pulledConormalUnitIso (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    pulledConormal (specMap (dualNumberToResidue Λ k)) hX ≅
      SheafOfModules.unit X.toRingedSpace.ringCatSheaf :=
  (hX.toShHom ^*).mapIso
      (conormalIdealIso (specMap (dualNumberToResidue Λ k))) ≪≫
    (hX.toShHom ^*).mapIso (residueKernelIsoUnit Λ k) ≪≫
    (hX.toShHom ^*).mapIso
      (unitIsoTensorUnit
        (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace) ≪≫
    pullbackUnitIso hX.toShHom ≪≫
    (unitIsoTensorUnit X.toRingedSpace).symm

/-- The forward map of `pulledConormalUnitIso` is pullback of the ε-coefficient iso. -/
theorem pulledConormalUnitIso_hom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (pulledConormalUnitIso Λ k X hX).hom =
      ((hX.toShHom ^*).mapIso
          (conormalIdealIso (specMap (dualNumberToResidue Λ k))) ≪≫
        (hX.toShHom ^*).mapIso (residueKernelIsoUnit Λ k) ≪≫
        (hX.toShHom ^*).mapIso
          (unitIsoTensorUnit
            (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace) ≪≫
        pullbackUnitIso hX.toShHom ≪≫
        (unitIsoTensorUnit X.toRingedSpace).symm).hom := sorry

/-- The inverse map of `pulledConormalUnitIso` is pullback of the map `a ↦ a·ε`. -/
theorem pulledConormalUnitIso_inv (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (pulledConormalUnitIso Λ k X hX).inv =
      ((hX.toShHom ^*).mapIso
          (conormalIdealIso (specMap (dualNumberToResidue Λ k))) ≪≫
        (hX.toShHom ^*).mapIso (residueKernelIsoUnit Λ k) ≪≫
        (hX.toShHom ^*).mapIso
          (unitIsoTensorUnit
            (Spec (CommRingCat.of (residue Λ k).carrier)).toRingedSpace) ≪≫
        pullbackUnitIso hX.toShHom ≪≫
        (unitIsoTensorUnit X.toRingedSpace).symm).inv := sorry

/-- Ext⁰ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extZero (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :=
  Ext⁽(0 : ℤ)⁾((moduleQ X.toRingedSpace).obj NL[hX.toShHom],
    (moduleQ X.toRingedSpace).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

/-- Ext¹ of the naive cotangent complex of `X / k` against `𝒪_X[0]`. -/
abbrev extOne (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :=
  Ext⁽(1 : ℤ)⁾((moduleQ X.toRingedSpace).obj NL[hX.toShHom],
    (moduleQ X.toRingedSpace).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

/-- Morphisms `Ω_{X/k} ⟶ 𝒪_X`. -/
abbrev homOmega (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :=
  Ω[hX.toShHom] ⟶ SheafOfModules.unit X.toRingedSpace.ringCatSheaf

/-- Derivations `Der_k(𝒪_X, 𝒪_X)`. -/
abbrev derivations (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :=
  RingedSpace.Hom.derivations hX.toShHom
    (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)

/-- Transport of an Ext class along `pulledConormalUnitIso`, in degree `n`. -/
def extNLMap (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (n : ℤ)
    {F G : X.toRingedSpace.Modules} (φ : F ⟶ G) :
    Ext⁽n⁾((moduleQ X.toRingedSpace).obj NL[hX.toShHom],
        (moduleQ X.toRingedSpace).obj
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj F)) →
      Ext⁽n⁾((moduleQ X.toRingedSpace).obj NL[hX.toShHom],
        (moduleQ X.toRingedSpace).obj
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj G)) :=
  fun ξ ↦ ξ ≫ (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) n).map
    ((moduleQ X.toRingedSpace).map
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map φ))

/-- Transport Ext⁰ of `f^* 𝒞` to Ext⁰ of `𝒪_X`. -/
def extZeroOfNL (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX]
    (ξ : extZeroNL (specMap (dualNumberToResidue Λ k)) hX) :
    extZero Λ k X hX :=
  extNLMap Λ k X hX (0 : ℤ) (pulledConormalUnitIso Λ k X hX).hom ξ

/-- Transport Ext⁰ of `𝒪_X` to Ext⁰ of `f^* 𝒞`. -/
def extZeroNLOf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (ξ : extZero Λ k X hX) :
    extZeroNL (specMap (dualNumberToResidue Λ k)) hX :=
  extNLMap Λ k X hX (0 : ℤ) (pulledConormalUnitIso Λ k X hX).inv ξ

/-- Transport Ext¹ of `𝒪_X` to Ext¹ of `f^* 𝒞`. -/
def extOneNLOf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (ξ : extOne Λ k X hX) :
    extOneNL (specMap (dualNumberToResidue Λ k)) hX :=
  extNLMap Λ k X hX (1 : ℤ) (pulledConormalUnitIso Λ k X hX).inv ξ

/-- The scheme automorphism of `X'` underlying an infinitesimal automorphism of `X`. -/
def infSchemeHom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (α : inf Λ k X hX) :
    trivialScheme Λ k X hX ⟶ trivialScheme Λ k X hX :=
  (fiberInclusion.map α.val.hom).schemeHom

/-- Automorphisms of the trivial lift reducing to the identity on `X`, from `Inf(Def_X)`. -/
def infToReduceIdAuto (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (α : inf Λ k X hX) :
    ReduceIdAuto (trivialFlatLift Λ k X hX) where
  hom := infSchemeHom Λ k X hX α
  over := sorry
  restrict := sorry
  isIso := sorry

/-- `infToReduceIdAuto` records the underlying scheme automorphism of `α`. -/
theorem infToReduceIdAuto_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (α : inf Λ k X hX) :
    (infToReduceIdAuto Λ k X hX α).hom = infSchemeHom Λ k X hX α := sorry

/-- The comparison `Inf(Def_X) ⟶ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`. -/
def infToExtZero (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    inf Λ k X hX → extZero Λ k X hX :=
  fun α ↦ extZeroOfNL Λ k X hX
    (reduceIdAutoEquiv (trivialFlatLift Λ k X hX) (infToReduceIdAuto Λ k X hX α))

/-- `infToExtZero` is `reduceIdAutoEquiv` of `infToReduceIdAuto`, transported to `𝒪_X`. -/
theorem infToExtZero_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (α : inf Λ k X hX) :
    infToExtZero Λ k X hX α =
      extZeroOfNL Λ k X hX
        (reduceIdAutoEquiv (trivialFlatLift Λ k X hX) (infToReduceIdAuto Λ k X hX α)) := sorry

/-- The comparison `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ⟶ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`,
assembled from `homologyZeroIso` and the degree-zero Hom/Ext chart of
`FlatLift.homOmegaExtZeroInv`. -/
def extZeroToHomOmegaOfUnit (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (ξ : extZero Λ k X hX) :
    homOmega Λ k X hX :=
  (RingedSpace.NaiveCotangent.homologyZeroIso hX.toShHom).inv ≫
    (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (0 : ℤ)).inv.app
      NL[hX.toShHom] ≫
    (DerivedCategory.homologyFunctor X.toRingedSpace.Modules (0 : ℤ)).map
      ((CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        X.toRingedSpace.Modules (0 : ℤ)).hom.app
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)

/-- The comparison `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ⟶ Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`,
via the canonical augmentation of `NL_{X/k}` and the degree-zero Ext chart. -/
def homOmegaToExtZeroOfUnit (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (α : homOmega Λ k X hX) :
    extZero Λ k X hX :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
    ((moduleQ X.toRingedSpace).map
      (RingedSpace.NaiveCotangent.augmentation hX.toShHom ≫
        (CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map α) ≫
      (DerivedCategory.singleFunctorIsoCompQ X.toRingedSpace.Modules (0 : ℤ)).hom.app
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))

/-- The comparison `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ≃ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`. -/
def extZeroEquivHomOmega (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    extZero Λ k X hX ≃ homOmega Λ k X hX where
  toFun ξ := extZeroToHomOmegaOfUnit Λ k X hX ξ
  invFun α := homOmegaToExtZeroOfUnit Λ k X hX α
  left_inv := sorry
  right_inv := sorry

/-- `extZeroEquivHomOmega` sends an Ext⁰ class to the corresponding map out of `Ω_{X/k}`. -/
theorem extZeroEquivHomOmega_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (ξ : extZero Λ k X hX) :
    extZeroEquivHomOmega Λ k X hX ξ = extZeroToHomOmegaOfUnit Λ k X hX ξ := sorry

/-- The comparison `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ≃ Der_k(𝒪_X, 𝒪_X)`. -/
def homOmegaEquivDer (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    homOmega Λ k X hX ≃ derivations Λ k X hX :=
  RingedSpace.Hom.homEquiv hX.toShHom
    (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)

/-- `homOmegaEquivDer` is the representing equivalence of Lemma 29.32.2. -/
theorem homOmegaEquivDer_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    (α : homOmega Λ k X hX) :
    homOmegaEquivDer Λ k X hX α =
      RingedSpace.Hom.homEquiv hX.toShHom
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) α := sorry

/-- The dual-number fibre object of `Def_X` associated to a flat first-order lift. -/
def ofFlatLift (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX]
    (L : FlatLift (specMap (dualNumberToResidue Λ k)) hX) :
    (deformationForget Λ k X hX).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X hX).obj
        (Over.mk
          (Hom.of (dualNumberToResidue Λ k) L.i L.isPullback.flip :
            of (dualNumber Λ k) L.space L.f' ⟶
              fiberInclusion.obj (residueObj Λ k X hX))) =
      dualNumber Λ k)

/-- Isomorphism classes of flat lifts map to tangent vectors of `Def_X`. -/
def ofIsoClass (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    IsoClass (specMap (dualNumberToResidue Λ k)) hX → tangentSpace Λ k X hX :=
  Quotient.lift (fun L ↦ tangentSpaceMk Λ k X hX (ofFlatLift Λ k X hX L)) sorry

/-- The class of a lift is sent to the class of `ofFlatLift`. -/
theorem ofIsoClass_mk (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX]
    (L : FlatLift (specMap (dualNumberToResidue Λ k)) hX) :
    ofIsoClass Λ k X hX (isoClassMk L) =
      tangentSpaceMk Λ k X hX (ofFlatLift Λ k X hX L) := sorry

/-- The comparison `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X) ⟶ T Def_X`. -/
def ofExtOne (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    extOne Λ k X hX → tangentSpace Λ k X hX :=
  fun ξ ↦ ofIsoClass Λ k X hX
    (isoClassEquiv (trivialFlatLift Λ k X hX) (extOneNLOf Λ k X hX ξ))

/-- `ofExtOne` sends an Ext¹ class to the translate of the trivial lift. -/
theorem ofExtOne_apply (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (ξ : extOne Λ k X hX) :
    ofExtOne Λ k X hX ξ =
      ofIsoClass Λ k X hX
        (isoClassEquiv (trivialFlatLift Λ k X hX) (extOneNLOf Λ k X hX ξ)) := sorry

/-- The zero Ext¹ class is sent to the trivial tangent vector. -/
theorem ofExtOne_zero (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    ofExtOne Λ k X hX 0 = trivialTangent Λ k X hX := sorry

end FlatSchemeCat
