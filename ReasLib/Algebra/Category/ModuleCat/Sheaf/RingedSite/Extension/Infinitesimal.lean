/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallySurjective

/-!
# Infinitesimal maps for mixed-scalar extensions

This module constructs the kernel-action descent and the canonical infinitesimal map associated to
a mixed-scalar extension on a locally surjective square-zero thickening.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option backward.privateInPublic true

universe u v w

namespace SheafOfModules.RingedSite
namespace FirstOrderThickening

section ExtensionAction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}

variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The kernel-ideal action on the middle term is killed by the quotient map. -/
theorem action_comp_p (E : Extension π) :
    IdealSheaf.action (KernelIdeal.subobject π) E.middle ≫ E.p = 0 := sorry

/-- The kernel-ideal action on the middle term, lifted through the kernel of the quotient map. -/
noncomputable def actionLift (E : Extension π) :
    moduleTensor (KernelIdeal.sheaf π) E.middle ⟶
      (restrictionAlong π).obj E.kernel :=
  have := E.shortExact.mono_f
  E.shortExact.exact.lift
    (IdealSheaf.action (KernelIdeal.subobject π) E.middle) (action_comp_p E)

/-- The lifted action vanishes after precomposition with the tensor of the inclusion. -/
theorem tensorι_comp_actionLift (E : Extension π) :
    (tensorLeft (KernelIdeal.sheaf π)).map E.ι ≫ actionLift E = 0 := sorry

/-- Tensoring the quotient map with the kernel ideal yields an epimorphism. -/
theorem tensor_p_epi (E : Extension π) :
    Epi ((shortComplex E).map (tensorLeft (KernelIdeal.sheaf π))).g := sorry

/-- The sequence obtained by tensoring a mixed-scalar extension with the kernel ideal is exact. -/
theorem tensorSequence_exact (E : Extension π) :
    ((shortComplex E).map (tensorLeft (KernelIdeal.sheaf π))).Exact := sorry

/-- The source-ring-linear infinitesimal comparison before descending the kernel ideal. -/
noncomputable def infMapPushforward (E : Extension π) :
    moduleTensor (KernelIdeal.sheaf π) ((restrictionAlong π).obj E.quot) ⟶
      (restrictionAlong π).obj E.kernel :=
  have := tensor_p_epi E
  (tensorSequence_exact E).desc (actionLift E) (tensorι_comp_actionLift E)

/-- The local formula for the source-ring-linear infinitesimal comparison. -/
theorem infMapPushforward_spec (E : Extension π) (U : Cᵒᵖ)
    (f : (KernelIdeal.sheaf π).val.obj U)
    (s : ((restrictionAlong π).obj E.quot).val.obj U)
    (s' : E.middle.val.obj U)
    (hs : (E.p.val.app U).hom s' = s) :
    (E.ι.val.app U).hom
        (((infMapPushforward E).val.app U).hom (tensorSection 𝒪' U f s)) =
      KernelIdeal.ιApp π U f • s' := sorry

end ExtensionAction

section KernelModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{w}} {π : 𝒪' ⟶ 𝒪}

variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- The kernel ideal regarded as an 𝒪-module after square-zero descent. -/
noncomputable abbrev idealModule (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  hπ.targetModule (KernelIdeal.quotientComparison_isIso π)

/-- The underlying additive map from the descended kernel module to the kernel ideal sheaf. -/
noncomputable def restrictIdealModuleHom_toPresheaf (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    ((restrictionAlong π).obj (idealModule hπ)).val.presheaf ⟶
      (KernelIdeal.sheaf π).val.presheaf :=
  (hπ.targetModuleForgetIso (KernelIdeal.quotientComparison_isIso π)).hom.hom

/-- The underlying additive inverse map from the kernel ideal sheaf to the descended module. -/
noncomputable def restrictIdealModuleInv_toPresheaf (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    (KernelIdeal.sheaf π).val.presheaf ⟶
      ((restrictionAlong π).obj (idealModule hπ)).val.presheaf :=
  (hπ.targetModuleForgetIso (KernelIdeal.quotientComparison_isIso π)).inv.hom

/-- The forward additive comparison is linear over the source ring sheaf. -/
theorem restrictIdealModuleHom_smul (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪').obj.obj U)
    (m : ((restrictionAlong π).obj (idealModule hπ)).val.obj U) :
    (restrictIdealModuleHom_toPresheaf hπ).app U (r • m) =
      r • (restrictIdealModuleHom_toPresheaf hπ).app U m :=
  hπ.targetModuleRestrictHom_smul (KernelIdeal.quotientComparison_isIso π) U r m

/-- The inverse additive comparison is linear over the source ring sheaf. -/
theorem restrictIdealModuleInv_smul (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪').obj.obj U)
    (m : (KernelIdeal.sheaf π).val.obj U) :
    (restrictIdealModuleInv_toPresheaf hπ).app U (r • m) =
      r • (restrictIdealModuleInv_toPresheaf hπ).app U m :=
  hπ.targetModuleRestrictInv_smul (KernelIdeal.quotientComparison_isIso π) U r m

/-- The source-ring-linear map from the descended kernel module to the kernel ideal sheaf. -/
noncomputable def restrictIdealModuleHom (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    (restrictionAlong π).obj (idealModule hπ) ⟶ KernelIdeal.sheaf π :=
  (hπ.targetModuleRestrictIso (KernelIdeal.quotientComparison_isIso π)).hom

/-- The inverse source-ring-linear map from the kernel ideal sheaf to the descended module. -/
noncomputable def restrictIdealModuleInv (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    KernelIdeal.sheaf π ⟶ (restrictionAlong π).obj (idealModule hπ) :=
  (hπ.targetModuleRestrictIso (KernelIdeal.quotientComparison_isIso π)).inv

/-- The forward and inverse comparisons compose to the identity on the restricted descended module. -/
theorem restrictIdealModuleHom_inv_id (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    restrictIdealModuleHom hπ ≫ restrictIdealModuleInv hπ = 𝟙 _ :=
  (hπ.targetModuleRestrictIso (KernelIdeal.quotientComparison_isIso π)).hom_inv_id

/-- The inverse and forward comparisons compose to the identity on the kernel ideal sheaf. -/
theorem restrictIdealModuleInv_hom_id (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    restrictIdealModuleInv hπ ≫ restrictIdealModuleHom hπ = 𝟙 _ :=
  (hπ.targetModuleRestrictIso (KernelIdeal.quotientComparison_isIso π)).inv_hom_id

/-- Restriction of scalars of the descended kernel module recovers the kernel ideal sheaf. -/
noncomputable def restrictIdealModuleIso (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    (restrictionAlong π).obj (idealModule hπ) ≅ KernelIdeal.sheaf π :=
  hπ.targetModuleRestrictIso (KernelIdeal.quotientComparison_isIso π)

end KernelModule

section ExtensionTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}

variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]

private abbrev tensorComparisonReverseTarget (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :=
  moduleTensor ((restrictionAlong π).obj (idealModule hπ))
    ((restrictionAlong π).obj E.quot)

private def tensorComparisonReversePair (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) (U : Cᵒᵖ) :
    (idealModule hπ).val.obj U →+ E.quot.val.obj U →+
      (tensorComparisonReverseTarget hπ E).val.obj U :=
  let t := tensorSectionLinear 𝒪' ((restrictionAlong π).obj (idealModule hπ))
    ((restrictionAlong π).obj E.quot) U
  { toFun x := (t x).toAddMonoidHom
    map_zero' := by ext y; exact congrArg (fun f ↦ f y) t.map_zero
    map_add' := by intro x y; ext z; exact congrArg (fun f ↦ f z) (t.map_add x y) }

private def tensorComparisonReverseBalanced (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) : Prop :=
  ∀ U (r : 𝒪.obj.obj U) (x : (idealModule hπ).val.obj U) (y : E.quot.val.obj U),
    tensorComparisonReversePair hπ E U (r • x) y =
      tensorComparisonReversePair hπ E U x (r • y)

private def tensorComparisonReverseApp (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π)
    (p : tensorComparisonReverseBalanced hπ E) (U : Cᵒᵖ) :=
  TensorProduct.liftAddHom (tensorComparisonReversePair hπ E U) (p U)

private def tensorComparisonReversePresheafLaws (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π)
    (p : tensorComparisonReverseBalanced hπ E) : Prop :=
  (∀ U (r : 𝒪'.obj.obj U)
      (x : ((PresheafOfModules.restrictScalars (ringSheafMap π).hom).obj
        (PresheafOfModules.Monoidal.tensorObj (idealModule hπ).val E.quot.val)).obj U),
    tensorComparisonReverseApp hπ E p U (r • x) =
      r • tensorComparisonReverseApp hπ E p U x) ∧
  (∀ U V (f : U ⟶ V)
      (x : ((PresheafOfModules.restrictScalars (ringSheafMap π).hom).obj
        (PresheafOfModules.Monoidal.tensorObj (idealModule hπ).val E.quot.val)).obj U),
    tensorComparisonReverseApp hπ E p V
        ((((PresheafOfModules.restrictScalars (ringSheafMap π).hom).obj
          (PresheafOfModules.Monoidal.tensorObj (idealModule hπ).val E.quot.val)).map f) x) =
      ((tensorComparisonReverseTarget hπ E).val.map f)
        (tensorComparisonReverseApp hπ E p U x))

/-- The reverse pure-tensor assignment is balanced over quotient scalars and commutes with
restriction; balance is checked after locally lifting those scalars through the projection. -/
private theorem tensorComparison_idealInv_wellDefined (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    tensorComparisonReverseBalanced hπ E ∧
      ∀ p : tensorComparisonReverseBalanced hπ E,
        tensorComparisonReversePresheafLaws hπ E p := sorry

private def tensorComparisonReversePresheaf (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    (PresheafOfModules.restrictScalars (ringSheafMap π).hom).obj
        (PresheafOfModules.Monoidal.tensorObj (idealModule hπ).val E.quot.val) ⟶
      (tensorComparisonReverseTarget hπ E).val where
  app U := @ModuleCat.ofHom _ _ _ _ _
    (((PresheafOfModules.restrictScalars (ringSheafMap π).hom).obj
      (PresheafOfModules.Monoidal.tensorObj (idealModule hπ).val E.quot.val)).obj U).isModule
    _ ((tensorComparisonReverseTarget hπ E).val.obj U).isModule
    { toFun := tensorComparisonReverseApp hπ E
        (tensorComparison_idealInv_wellDefined hπ E).1 U
      map_add' := (tensorComparisonReverseApp hπ E
        (tensorComparison_idealInv_wellDefined hπ E).1 U).map_add
      map_smul' := ((tensorComparison_idealInv_wellDefined hπ E).2 (tensorComparison_idealInv_wellDefined hπ E).1).1 U }
  naturality {U V} f := by
    ext x
    exact ((tensorComparison_idealInv_wellDefined hπ E).2 (tensorComparison_idealInv_wellDefined hπ E).1).2 U V f x

/-- The reverse restriction-tensor comparison sends a pure tensor to the pure tensor of the
same sections and descends this balanced assignment through module sheafification. -/
def tensorComparison_idealInv (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    (restrictionAlong π).obj (moduleTensor (idealModule hπ) E.quot) ⟶
      moduleTensor ((restrictionAlong π).obj (idealModule hπ))
      ((restrictionAlong π).obj E.quot) :=
  (restrictionAlong π).map (ModuleSheafification.tensorObjIso 𝒪 (idealModule hπ) E.quot).hom ≫
    (ModuleSheafification.restrictionComponentIso π
      (PresheafOfModules.Monoidal.tensorObj (idealModule hπ).val E.quot.val)).inv ≫
    (moduleSheafificationHomEquiv 𝒪' _ _).symm
      (tensorComparisonReversePresheaf hπ E)

/-- The two restriction-tensor comparisons are mutually inverse. -/
theorem tensorComparison_idealInv_laws (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    Restriction.tensorComparison π (idealModule hπ) E.quot ≫
        tensorComparison_idealInv hπ E = 𝟙 _ ∧
      tensorComparison_idealInv hπ E ≫
        Restriction.tensorComparison π (idealModule hπ) E.quot = 𝟙 _ := sorry

/-- Restriction of scalars through a locally surjective square-zero projection commutes with
tensoring the descended kernel module and the quotient module. -/
def tensorComparison_idealIso (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    moduleTensor ((restrictionAlong π).obj (idealModule hπ))
      ((restrictionAlong π).obj E.quot) ≅
      (restrictionAlong π).obj (moduleTensor (idealModule hπ) E.quot) where
  hom := Restriction.tensorComparison π (idealModule hπ) E.quot
  inv := tensorComparison_idealInv hπ E
  hom_inv_id := (tensorComparison_idealInv_laws hπ E).1
  inv_hom_id := (tensorComparison_idealInv_laws hπ E).2

/-- After square-zero descent, the restriction tensor comparison for the kernel module and quotient
module is an isomorphism. -/
theorem tensorComparison_ideal_isIso (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    IsIso (Restriction.tensorComparison π (idealModule hπ) E.quot) :=
  (tensorComparison_idealIso hπ E).isIso_hom

/-- The canonical target-ring-linear infinitesimal map associated to a mixed-scalar extension. -/
noncomputable def infMap (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    moduleTensor (idealModule hπ) E.quot ⟶ E.kernel :=
  (restrictHomEquivOfIsLocallySurjective (ringSheafMap π)
      (moduleTensor (idealModule hπ) E.quot) E.kernel).symm
    ((tensorComparison_idealIso hπ E).inv ≫
      moduleTensorMap (restrictIdealModuleIso hπ).hom (𝟙 _) ≫
      infMapPushforward E)

/-- The local formula characterizing the target-ring-linear infinitesimal map. -/
theorem infMap_spec (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) (U : Cᵒᵖ)
    (f : (idealModule hπ).val.obj U) (s : E.quot.val.obj U)
    (s' : E.middle.val.obj U) (hs : (E.p.val.app U).hom s' = s)
    (k : E.kernel.val.obj U)
    (hk : (E.ι.val.app U).hom k =
      KernelIdeal.ιApp π U (((restrictIdealModuleIso hπ).hom.val.app U).hom f) • s') :
    ((infMap hπ E).val.app U).hom (tensorSection 𝒪 U f s) = k := sorry

end ExtensionTensor

end FirstOrderThickening
end SheafOfModules.RingedSite
