/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DividedPower.ExteriorCalculus
public import ReasLib.AlgebraicGeometry.Crystalline.FirstOrder
public import ReasLib.AlgebraicGeometry.Crystalline.SecondOrder
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorScalarExtension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials

/-!
# The connection of a crystal of modules

The crystal transition on the split divided-power first-order thickening induces
a connection valued in the sheaf tensor with divided-power relative differentials.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation TensorProduct

noncomputable section

universe u

namespace CrystallineModuleSheaf.CrisModuleSheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Global functions on a crystalline thickening. -/
abbrev sectionRing (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Γ(T.obj.1.thickening, ⊤)

/-- Global sections of a crystalline module on a thickening. -/
abbrev sectionModule (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) := Γ(F.obj T, ⊤)

/-- Global sections of the canonical divided-power relative differential sheaf. -/
abbrev oneForms (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Γ((CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module, ⊤)

/-- The structure morphism gives global functions their canonical algebra over base functions. -/
instance sectionRingAlgebra (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Algebra Γ(S, ⊤) (sectionRing T) :=
  (T.obj.1.thickeningToBase.app ⊤).hom.toAlgebra

/-- The relative derivation followed by the canonical divided-power relation quotient. -/
def universalDerivation (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  (d[T.obj.1.thickeningToBase.toShHom]).postcomp
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).quotient.val

/-- The universal divided-power derivation applies the quotient to the ordinary differential. -/
theorem universalDerivation_apply (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (a : T.obj.1.thickening.presheaf.obj U) :
    (universalDerivation T).d a =
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).quotient.val.app U
        ((d[T.obj.1.thickeningToBase.toShHom]).d a) := rfl

/-- The crystal comparison along the constant first-order projection. -/
def comparisonP0 (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  F.comparison (CrystallineObject.DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T)

/-- The crystal comparison along the divided-power Taylor projection. -/
def comparisonP1 (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  F.comparison (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T)

/-- The transition from constant pullback to Taylor pullback of a crystal. -/
def crystalTransition (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  comparisonP0 F T ≫
    inv (F.comparison
      (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T))

/-- The canonical divided-power exterior calculus on a crystalline thickening. -/
def exteriorCalculus (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  DividedPowerScheme.RelativeDifferentials.exteriorCalculus
    (CrystallineObject.DividedPowerSecondOrderThickening.dividedPowerScheme T)
    S T.obj.1.thickeningToBase

-- Visibility justification: these coordinate models are private implementations of
-- the geometric pullback, rather than additional public module-sheaf constructions.
set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorModel (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  SheafOfModules.TensorScalarExtension.functor
    (ringSheafMap (J := Opens.grothendieckTopology T.obj.1.thickening)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T))
    (fun U a b ↦ @mul_comm (T.obj.1.thickening.presheaf.obj U) _ a b)
    (fun U a b ↦ @mul_comm ((CrystallineObject.DividedPowerFirstOrderThickening.sheaf T).obj.obj U) _ a b)

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorModelIso (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Scheme.Modules.pullback
      (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening ≅
        taylorModel T :=
  Adjunction.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction
      (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening)
    (SheafOfModules.TensorScalarExtension.adjunction
      (ringSheafMap (J := Opens.grothendieckTopology T.obj.1.thickening)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T))
      (fun U a b ↦ @mul_comm (T.obj.1.thickening.presheaf.obj U) _ a b)
    (fun U a b ↦ @mul_comm ((CrystallineObject.DividedPowerFirstOrderThickening.sheaf T).obj.obj U) _ a b))

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private abbrev taylorCoefficients (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) :
    ModuleCat (T.obj.1.thickening.presheaf.obj U) :=
  (ModuleCat.restrictScalars
    ((CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T).hom.app U).hom).obj
      (ModuleCat.of ((CrystallineObject.DividedPowerFirstOrderThickening.sheaf T).obj.obj U)
        ((CrystallineObject.DividedPowerFirstOrderThickening.sheaf T).obj.obj U))

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorCoordinate (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (r : taylorCoefficients T U) :
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module.val.obj U :=
  r.2 - (universalDerivation T).d r.1

set_option backward.privateInPublic true in
private def taylorCoordinateLaws (T : smallCrystallineSite S I γ h_compatible X x₀) : Prop :=
  (∀ (U : (Opens T.obj.1.thickening)ᵒᵖ) (r s : taylorCoefficients T U),
    taylorCoordinate T U (r + s) = taylorCoordinate T U r + taylorCoordinate T U s) ∧
  (∀ (U : (Opens T.obj.1.thickening)ᵒᵖ) (a : T.obj.1.thickening.presheaf.obj U)
      (r : taylorCoefficients T U),
    taylorCoordinate T U (a • r) = a • taylorCoordinate T U r)

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorCoordinateLinear (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h : taylorCoordinateLaws T)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) :
    taylorCoefficients T U →ₗ[T.obj.1.thickening.presheaf.obj U]
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module.val.obj U where
  toFun := taylorCoordinate T U
  map_add' := h.1 U
  map_smul' := h.2 U

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorRaw (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  PresheafOfModules.SameSiteTensorExtension.obj
    (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T).hom (F.obj T).val

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorRawIso (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (Scheme.Modules.pullback
      (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
        (F.obj T) ≅
      (moduleSheafification (CrystallineObject.DividedPowerFirstOrderThickening.sheaf T)).obj
        (taylorRaw F T) :=
  (taylorModelIso T).app (F.obj T)

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorTensorCoordinate (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) (h : taylorCoordinateLaws T)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      (ringSheafMap (J := Opens.grothendieckTopology T.obj.1.thickening)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).hom).obj
          (taylorRaw F T)).obj U →ₗ[T.obj.1.thickening.presheaf.obj U]
      (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module).val.obj U :=
  TensorProduct.lift
    ((tensorSectionLinear T.obj.1.thickening.sheaf (F.obj T)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module U).flip.comp
        (taylorCoordinateLinear T h U))

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorCoordinateComponent (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) (h : taylorCoordinateLaws T)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      (ringSheafMap (J := Opens.grothendieckTopology T.obj.1.thickening)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).hom).obj
          (taylorRaw F T)).obj U ⟶
    (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module).val.obj U :=
  ModuleCat.ofHom
    (X := ((PresheafOfModules.restrictScalars
      (ringSheafMap (J := Opens.grothendieckTopology T.obj.1.thickening)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).hom).obj
          (taylorRaw F T)).obj U)
    (Y := (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module).val.obj U)
    (taylorTensorCoordinate F T h U)

set_option backward.privateInPublic true in
/-- The Taylor differential coordinate is linear, and its tensor extension is compatible
with every open restriction. -/
theorem tensorKernelInv_laws (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    taylorCoordinateLaws T ∧
    ∀ (h : taylorCoordinateLaws T) {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V),
      ((PresheafOfModules.restrictScalars
        (ringSheafMap (J := Opens.grothendieckTopology T.obj.1.thickening)
          (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).hom).obj
            (taylorRaw F T)).map ρ ≫
        (ModuleCat.restrictScalars (T.obj.1.thickening.presheaf.map ρ).hom).map
          (taylorCoordinateComponent F T h V) =
      taylorCoordinateComponent F T h U ≫
        (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
          (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module).val.map ρ := sorry

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def taylorCoordinatePresheaf (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (PresheafOfModules.restrictScalars
      (ringSheafMap (J := Opens.grothendieckTopology T.obj.1.thickening)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).hom).obj
          (taylorRaw F T) ⟶
      (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module).val where
  app U := taylorCoordinateComponent F T (tensorKernelInv_laws F T).1 U
  naturality := (tensorKernelInv_laws F T).2 (tensorKernelInv_laws F T).1

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
/-- The differential-coordinate projection on the Taylor pullback, after sheaf tensor
descent; its restriction to the reduction kernel is the inverse kernel comparison. -/
def tensorKernelProjection (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).obj
      ((Scheme.Modules.pullback
        (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
          (F.obj T)) ⟶
      moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module :=
  (restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).map
      (taylorRawIso F T).hom ≫
    (ModuleSheafification.restrictionIso
      (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).inv.app _ ≫
    (moduleSheafificationHomEquiv T.obj.1.thickening.sheaf _ _).symm
      (taylorCoordinatePresheaf F T)

set_option backward.privateInPublic true in
private def ordinaryDifferentialsPullback
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :=
  RingedSpace.Hom.Differentials.comparison
    (show CommSq f.hom.thickening.toShHom T.obj.1.thickeningToBase.toShHom
      U.obj.1.thickeningToBase.toShHom (𝟙 S.toRingedSpace) from
      ⟨by
        rw [Category.comp_id, ← LocallyRingedSpace.comp_toShHom]
        exact congrArg (fun g : T.obj.1.thickening ⟶ S ↦ g.toShHom) f.hom.base_comm⟩)

set_option backward.privateInPublic true in
/-- Pullback of the ordinary differential quotient sends its kernel to divided-power
relations, so the canonical differential comparison descends. -/
theorem differentialsPullback_relations
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :
    kernel.ι ((Scheme.Modules.pullback f.hom.thickening).map
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials U).quotient) ≫
      ordinaryDifferentialsPullback f ≫
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).quotient = 0 := sorry

set_option backward.privateInPublic true in
/-- The canonical crystalline pullback comparison on divided-power differential sheaves. -/
def differentialsPullback
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :
    (Scheme.Modules.pullback f.hom.thickening).obj
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials U).module ⟶
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module := by
  have hq : Epi (CrystallineObject.DividedPowerFirstOrderThickening.differentials U).quotient := by
    change Epi (cokernel.π _)
    infer_instance
  exact @Abelian.epiDesc _ _ _ _ _
    ((Scheme.Modules.pullback f.hom.thickening).map
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials U).quotient)
    (@Functor.map_epi _ _ _ _ (Scheme.Modules.pullback f.hom.thickening) inferInstance _ _ _ hq)
    _ (ordinaryDifferentialsPullback f ≫
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).quotient)
    (differentialsPullback_relations f)

/-- The differential comparison for an identity is the canonical identity-pullback map. -/
theorem differentialsPullback_id (T : smallCrystallineSite S I γ h_compatible X x₀) :
    differentialsPullback (𝟙 T) = (Scheme.Modules.pullbackId T.obj.1.thickening).hom.app
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module := sorry

/-- Differential comparisons compose through the canonical pullback compositor. -/
theorem differentialsPullback_comp
    {T U V : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) (g : U ⟶ V) :
    differentialsPullback (f ≫ g) =
      (Scheme.Modules.pullbackComp f.hom.thickening g.hom.thickening).inv.app
          (CrystallineObject.DividedPowerFirstOrderThickening.differentials V).module ≫
        (Scheme.Modules.pullback f.hom.thickening).map (differentialsPullback g) ≫
          differentialsPullback f := sorry

set_option backward.privateInPublic true in
private abbrev taylorPullback (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  (Scheme.Modules.pullback
    (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T)

set_option backward.privateInPublic true in
private abbrev taylorRestricted (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  (restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).obj
    (taylorPullback F T)

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
private def reductionIdentity (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    F.obj T ≅
      (restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).obj
        ((restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.projection T)).obj
          (F.obj T)) where
  hom := ⟨{
    app U := ModuleCat.ofHom
      (X := (F.obj T).val.obj U)
      (Y := ((restrictionAlong
        (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).obj
          ((restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.projection T)).obj
            (F.obj T))).val.obj U)
      { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    naturality := fun _ ↦ rfl }⟩
  inv := ⟨{
    app U := ModuleCat.ofHom
      (X := ((restrictionAlong
        (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).obj
          ((restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.projection T)).obj
            (F.obj T))).val.obj U)
      (Y := (F.obj T).val.obj U)
      { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    naturality := fun _ ↦ rfl }⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

set_option backward.privateInPublic true in
/-- Reduction of the Taylor pullback to the original module along the square-zero diagonal. -/
def firstOrderReduction (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    taylorRestricted F T ⟶ F.obj T :=
  (restrictionAlong (CrystallineObject.DividedPowerFirstOrderThickening.differentialLift T)).map
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).homEquiv _ _).symm (reductionIdentity F T).hom) ≫
    (reductionIdentity F T).inv

set_option backward.privateInPublic true in
private def pullbackSection {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules)
    (U : Opens Z) (m : M.val.obj (op U)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U) m

set_option backward.privateInPublic true in
private def pullbackP1Section (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (taylorPullback F T).val.obj U :=
  pullbackSection
    (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening
    (F.obj T) U.unop m

set_option backward.privateInPublic true in
private def transitionP0Section (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (taylorPullback F T).val.obj U :=
  (crystalTransition F T).val.app U
    (pullbackSection
      (CrystallineObject.DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T).hom.thickening
      (F.obj T) U.unop m)

set_option backward.privateInPublic true in
private def tensorKernelAction (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U)
    (ω : (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module.val.obj U) :
    (taylorRestricted F T).val.obj U :=
  ((taylorPullback F T).val.obj U).isModule.smul
    (show (CrystallineObject.DividedPowerFirstOrderThickening.sheaf T).obj.obj U from (0, ω))
    (pullbackP1Section F T U m)

set_option backward.privateInPublic true in
private def tensorKernelActionLaws (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) : Prop :=
  (∀ U m m' ω, tensorKernelAction F T U (m + m') ω =
    tensorKernelAction F T U m ω + tensorKernelAction F T U m' ω) ∧
  (∀ U m ω ω', tensorKernelAction F T U m (ω + ω') =
    tensorKernelAction F T U m ω + tensorKernelAction F T U m ω') ∧
  (∀ (U : (Opens T.obj.1.thickening)ᵒᵖ) (a : T.obj.1.thickening.presheaf.obj U) m ω, tensorKernelAction F T U (a • m) ω =
    a • tensorKernelAction F T U m ω) ∧
  (∀ (U : (Opens T.obj.1.thickening)ᵒᵖ) (a : T.obj.1.thickening.presheaf.obj U) m ω, tensorKernelAction F T U m (a • ω) =
    a • tensorKernelAction F T U m ω) ∧
  (∀ {U V} (ρ : U ⟶ V) m ω,
    (taylorRestricted F T).val.map ρ (tensorKernelAction F T U m ω) =
      tensorKernelAction F T V ((F.obj T).val.map ρ m)
        ((CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module.val.map ρ ω))

set_option backward.privateInPublic true in
private def tensorKernelPairing (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) (h : tensorKernelActionLaws F T) :
    SectionBilinearMap.{u, u} T.obj.1.thickening.sheaf (F.obj T)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module
      (taylorRestricted F T) where
  app U := {
    toFun m := {
      toFun := tensorKernelAction F T U m
      map_add' := h.2.1 U m
      map_smul' := fun a ω ↦ h.2.2.2.1 U a m ω }
    map_add' := by intro m m'; ext ω; exact h.1 U m m' ω
    map_smul' := by intro a m; ext ω; exact h.2.2.1 U a m ω }
  naturality := h.2.2.2.2

set_option backward.privateInPublic true in
/-- The square-zero action defines a restriction-compatible bilinear map annihilated by
reduction to the original module. -/
theorem tensorKernelHom_laws (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    tensorKernelActionLaws F T ∧
      ∀ h : tensorKernelActionLaws F T,
        (tensorKernelPairing F T h).hom ≫ firstOrderReduction F T = 0 := sorry

set_option backward.privateInPublic true in
/-- The square-zero action identifies module-valued one-forms with sections vanishing
under first-order reduction. -/
def tensorKernelHom (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module ⟶
      kernel (firstOrderReduction F T) :=
  kernel.lift _ (tensorKernelPairing F T (tensorKernelHom_laws F T).1).hom
    ((tensorKernelHom_laws F T).2 _)

/-- The inverse kernel comparison is the Taylor differential-coordinate projection. -/
def tensorKernelInv (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    kernel (firstOrderReduction F T) ⟶
      moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module :=
  kernel.ι _ ≫ tensorKernelProjection F T

/-- Acting by one-forms and then taking the Taylor coordinate is the identity. -/
theorem tensorKernelIso_hom_inv_id (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    tensorKernelHom F T ≫ tensorKernelInv F T = 𝟙 _ := sorry

/-- Taking the Taylor coordinate and then acting by one-forms recovers every reduction-kernel section. -/
theorem tensorKernelIso_inv_hom_id (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    tensorKernelInv F T ≫ tensorKernelHom F T = 𝟙 _ := sorry

/-- The first-order reduction kernel is canonically the sheaf tensor with divided-power differentials. -/
def tensorKernelIso (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
        (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module ≅
      kernel (firstOrderReduction F T) where
  hom := tensorKernelHom F T
  inv := tensorKernelInv F T
  hom_inv_id := tensorKernelIso_hom_inv_id F T
  inv_hom_id := tensorKernelIso_inv_hom_id F T

set_option backward.privateInPublic true in
/-- The difference between the Taylor pullback of a section and its constant pullback
transported by the crystal transition. -/
def connectionDifference (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (taylorRestricted F T).val.obj U :=
  pullbackP1Section F T U m - transitionP0Section F T U m

set_option backward.privateInPublic true in
/-- The crystal transition restricts to the identity along the square-zero diagonal. -/
theorem crystalTransition_diagonal (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (firstOrderReduction F T).val.app U (transitionP0Section F T U m) = m := sorry

/-- The first-order difference of a section vanishes under reduction to the diagonal. -/
theorem connectionDifference_mem_ker (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (firstOrderReduction F T).val.app U (connectionDifference F T U m) = 0 := sorry

/-- The connection value is the differential coordinate of the first-order crystal difference. -/
def canonicalConnectionValue (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module).val.obj U :=
  (tensorKernelProjection F T).val.app U (connectionDifference F T U m)

/-- The canonical connection is computed by the Taylor-coordinate projection of the
first-order difference. -/
theorem canonicalConnectionValue_spec (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    canonicalConnectionValue F T U m =
      (tensorKernelProjection F T).val.app U (connectionDifference F T U m) := rfl

/-- The canonical connection value is additive. -/
theorem canonicalConnectionValue_add (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m n : (F.obj T).val.obj U) :
    canonicalConnectionValue F T U (m + n) =
      canonicalConnectionValue F T U m + canonicalConnectionValue F T U n := sorry

/-- The canonical connection value is linear over the inverse-image base structure sheaf. -/
theorem canonicalConnectionValue_base_smul
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ)
    (a : (RingedSpace.DeRham.coefficients T.obj.1.thickeningToBase.toShHom).obj.obj U)
    (m : (F.obj T).val.obj U) :
    canonicalConnectionValue F T U
        ((RingedSpace.DeRham.structureMap T.obj.1.thickeningToBase.toShHom).hom.app U a • m) =
      (RingedSpace.DeRham.structureMap T.obj.1.thickeningToBase.toShHom).hom.app U a •
        canonicalConnectionValue F T U m := sorry

/-- The canonical connection value commutes with restriction to any open subset. -/
theorem canonicalConnectionValue_restrict
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    {U V : (Opens T.obj.1.thickening)ᵒᵖ} (ρ : U ⟶ V) (m : (F.obj T).val.obj U) :
    (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module).val.map ρ
        (canonicalConnectionValue F T U m) =
      canonicalConnectionValue F T V ((F.obj T).val.map ρ m) := sorry

/-- The coefficient-linear sheaf morphism underlying the canonical connection. -/
def canonicalConnectionHom (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (restrictionAlong (RingedSpace.DeRham.structureMap T.obj.1.thickeningToBase.toShHom)).obj
        (F.obj T) ⟶
      (restrictionAlong (RingedSpace.DeRham.structureMap T.obj.1.thickeningToBase.toShHom)).obj
        (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
          (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module) :=
  ⟨{
    app U := ModuleCat.ofHom
      (X := ((restrictionAlong (RingedSpace.DeRham.structureMap
        T.obj.1.thickeningToBase.toShHom)).obj (F.obj T)).val.obj U)
      (Y := ((restrictionAlong (RingedSpace.DeRham.structureMap
        T.obj.1.thickeningToBase.toShHom)).obj
          (moduleTensor (𝒪 := T.obj.1.thickening.sheaf) (F.obj T)
            (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module)).val.obj U)
      { toFun := canonicalConnectionValue F T U
        map_add' := canonicalConnectionValue_add F T U
        map_smul' := canonicalConnectionValue_base_smul F T U }
    naturality := by
      intro U V ρ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      exact (canonicalConnectionValue_restrict F T ρ m).symm }⟩

/-- The coefficient-linear connection morphism evaluates to the first-order coordinate value. -/
theorem canonicalConnectionHom_apply
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (canonicalConnectionHom F T).val.app U m = canonicalConnectionValue F T U m := rfl

/-- The canonical crystal connection satisfies the Leibniz rule for divided-power differentials. -/
theorem canonicalConnection_leibniz
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (a : T.obj.1.thickening.presheaf.obj U)
    (m : (F.obj T).val.obj U) :
    canonicalConnectionValue F T U (a • m) = a • canonicalConnectionValue F T U m +
      tensorSection T.obj.1.thickening.sheaf U m ((universalDerivation T).d a) := sorry

/-- The canonical connection of a crystal, valued in the sheaf tensor with divided-power differentials. -/
def canonicalConnection (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    SheafOfModules.RingedSite.Connection.{u, u}
      (RingedSpace.DeRham.structureMap T.obj.1.thickeningToBase.toShHom)
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module
      (universalDerivation T) (F.obj T) where
  hom := canonicalConnectionHom F T
  leibniz := canonicalConnection_leibniz F T

/-- Evaluation of the canonical sheaf connection is its first-order difference construction. -/
theorem canonicalConnection_apply (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U) :
    (canonicalConnection F T).apply U m = canonicalConnectionValue F T U m := rfl

/-- The canonical connection commutes with all crystalline morphisms on every open subset. -/
theorem canonicalConnection_naturality
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U)
    (V : Opens U.obj.1.thickening) (m : (F.obj U).val.obj (op V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f.hom.thickening).homEquiv _ _
      (schemeModulesTensorComparison f.hom.thickening (F.comparison f)
        (differentialsPullback f))).val.app (op V))
          ((canonicalConnection F U).apply (op V) m) =
      (canonicalConnection F T).apply (op (f.hom.thickening ⁻¹ᵁ V))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f.hom.thickening).homEquiv _ _
          (F.comparison f)).val.app (op V)) m) := sorry

set_option backward.privateInPublic true in
private def secondOrderTransition (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (a b : CrystallineObject.DividedPowerSecondOrderThickening.object I γ h_compatible x₀ T ⟶ T) :=
  F.comparison a ≫ inv (F.comparison b)

set_option backward.privateInPublic true in
private def transitionPullback {Y Z W : Scheme.{u}} (q : Y ⟶ Z) (a b : Z ⟶ W)
    (a' b' : Y ⟶ W) (ha : q ≫ a = a') (hb : q ≫ b = b')
    (M : W.Modules) (c : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj M) :
    (Scheme.Modules.pullback a').obj M ⟶ (Scheme.Modules.pullback b').obj M :=
  (Scheme.Modules.pullbackCongr ha).inv.app M ≫
    (Scheme.Modules.pullbackComp q a).inv.app M ≫
    (Scheme.Modules.pullback q).map c ≫
    (Scheme.Modules.pullbackComp q b).hom.app M ≫
    (Scheme.Modules.pullbackCongr hb).hom.app M

set_option backward.privateInPublic true in
private def pulledTransition (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (q : CrystallineObject.DividedPowerSecondOrderThickening.object I γ h_compatible x₀ T ⟶
      CrystallineObject.DividedPowerFirstOrderThickening.object I γ h_compatible x₀ T)
    (a b : CrystallineObject.DividedPowerSecondOrderThickening.object I γ h_compatible x₀ T ⟶ T)
    (ha : q ≫ CrystallineObject.DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T = a)
    (hb : q ≫ CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T = b) :
    (Scheme.Modules.pullback a.hom.thickening).obj (F.obj T) ⟶
      (Scheme.Modules.pullback b.hom.thickening).obj (F.obj T) :=
  transitionPullback q.hom.thickening
    (CrystallineObject.DividedPowerFirstOrderThickening.p₀ I γ h_compatible x₀ T).hom.thickening
    (CrystallineObject.DividedPowerFirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening
    a.hom.thickening b.hom.thickening
    (congrArg (fun f : CrystallineObject.DividedPowerSecondOrderThickening.object
      I γ h_compatible x₀ T ⟶ T ↦ f.hom.thickening) ha)
    (congrArg (fun f : CrystallineObject.DividedPowerSecondOrderThickening.object
      I γ h_compatible x₀ T ⟶ T ↦ f.hom.thickening) hb)
    (F.obj T) (crystalTransition F T)

set_option backward.privateInPublic true in
/-- The three pullbacks of the crystal transition on the second-order divided-power
thickening satisfy the ordered cocycle identity. -/
theorem crystalTransition_cocycle
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    let q0 := CrystallineObject.DividedPowerSecondOrderThickening.q₀ I γ h_compatible x₀ T
    let q1 := CrystallineObject.DividedPowerSecondOrderThickening.q₁ I γ h_compatible x₀ T
    let q2 := CrystallineObject.DividedPowerSecondOrderThickening.q₂ I γ h_compatible x₀ T
    (pulledTransition F T
      (CrystallineObject.DividedPowerSecondOrderThickening.q₀₁ I γ h_compatible x₀ T) q0 q1
      (CrystallineObject.DividedPowerSecondOrderThickening.q0_eq_q01_comp_p0 I γ h_compatible x₀ T)
      (CrystallineObject.DividedPowerSecondOrderThickening.q1_eq_q01_comp_p1 I γ h_compatible x₀ T) =
        secondOrderTransition F T q0 q1) ∧
    (pulledTransition F T
      (CrystallineObject.DividedPowerSecondOrderThickening.q₁₂ I γ h_compatible x₀ T) q1 q2
      (CrystallineObject.DividedPowerSecondOrderThickening.q1_eq_q12_comp_p0 I γ h_compatible x₀ T)
      (CrystallineObject.DividedPowerSecondOrderThickening.q2_eq_q12_comp_p1 I γ h_compatible x₀ T) =
        secondOrderTransition F T q1 q2) ∧
    (pulledTransition F T
      (CrystallineObject.DividedPowerSecondOrderThickening.q₀₂ I γ h_compatible x₀ T) q0 q2
      (CrystallineObject.DividedPowerSecondOrderThickening.q0_eq_q02_comp_p0 I γ h_compatible x₀ T)
      (CrystallineObject.DividedPowerSecondOrderThickening.q2_eq_q02_comp_p1 I γ h_compatible x₀ T) =
        secondOrderTransition F T q0 q2) ∧
    secondOrderTransition F T q0 q1 ≫ secondOrderTransition F T q1 q2 =
      secondOrderTransition F T q0 q2 := sorry

set_option backward.privateInPublic true in
set_option maxHeartbeats 1000000 in
/-- The second-order transition cocycle forces the curvature of the first-order
connection to vanish. The extended differential uses the exterior sign convention
in which the differential of a module-valued one-form is its connection wedge term
plus its coefficient tensor the differential of the form. -/
theorem canonicalConnection_curvature
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (hc : let q0 := CrystallineObject.DividedPowerSecondOrderThickening.q₀ I γ h_compatible x₀ T
          let q1 := CrystallineObject.DividedPowerSecondOrderThickening.q₁ I γ h_compatible x₀ T
          let q2 := CrystallineObject.DividedPowerSecondOrderThickening.q₂ I γ h_compatible x₀ T
          secondOrderTransition F T q0 q1 ≫ secondOrderTransition F T q1 q2 =
            secondOrderTransition F T q0 q2) :
    (∀ (U : (Opens T.obj.1.thickening)ᵒᵖ) (m : (F.obj T).val.obj U)
      (n : ℕ) (v : Fin n → (F.obj T).val.obj U)
      (ω : Fin n → (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module.val.obj U),
      (canonicalConnection F T).apply U m =
          ∑ i, tensorSection T.obj.1.thickening.sheaf U (v i) (ω i) →
      (SheafOfModules.RingedSite.Connection.differential.{u, u}
          (canonicalConnection F T) (exteriorCalculus T) 1).val.app U
          ((canonicalConnection F T).apply U m) =
        ∑ i, SheafOfModules.RingedSite.Connection.differentialPairing.{u, u}
          (canonicalConnection F T) (exteriorCalculus T) 1 U (v i) (ω i)) ∧
    (canonicalConnection F T).hom ≫
      SheafOfModules.RingedSite.Connection.differential.{u, u}
        (canonicalConnection F T) (exteriorCalculus T) 1 = 0 := sorry

end CrystallineModuleSheaf.CrisModuleSheaf

/-- Every crystal of modules has a canonical integrable connection with values in
the sheaf tensor with divided-power relative differentials. -/
theorem canonicalConnection_isIntegrable
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    SheafOfModules.RingedSite.Connection.IsIntegrable.{u, u}
      (CrystallineModuleSheaf.CrisModuleSheaf.canonicalConnection F T)
      (CrystallineModuleSheaf.CrisModuleSheaf.exteriorCalculus T) := sorry
