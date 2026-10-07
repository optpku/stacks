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

universe u v

namespace SheafOfModules.RingedSite
namespace FirstOrderThickening

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

variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]

/-- The kernel ideal regarded as an 𝒪-module after square-zero descent. -/
noncomputable abbrev idealModule (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪 :=
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
      r • (restrictIdealModuleHom_toPresheaf hπ).app U m := sorry

/-- The inverse additive comparison is linear over the source ring sheaf. -/
theorem restrictIdealModuleInv_smul (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪').obj.obj U)
    (m : (KernelIdeal.sheaf π).val.obj U) :
    (restrictIdealModuleInv_toPresheaf hπ).app U (r • m) =
      r • (restrictIdealModuleInv_toPresheaf hπ).app U m := sorry

/-- The source-ring-linear map from the descended kernel module to the kernel ideal sheaf. -/
noncomputable def restrictIdealModuleHom (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    (restrictionAlong π).obj (idealModule hπ) ⟶ KernelIdeal.sheaf π :=
  ⟨PresheafOfModules.homMk
    (restrictIdealModuleHom_toPresheaf hπ) (restrictIdealModuleHom_smul hπ)⟩

/-- The inverse source-ring-linear map from the kernel ideal sheaf to the descended module. -/
noncomputable def restrictIdealModuleInv (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    KernelIdeal.sheaf π ⟶ (restrictionAlong π).obj (idealModule hπ) :=
  ⟨PresheafOfModules.homMk
    (restrictIdealModuleInv_toPresheaf hπ) (restrictIdealModuleInv_smul hπ)⟩

/-- The forward and inverse comparisons compose to the identity on the restricted descended module. -/
theorem restrictIdealModuleHom_inv_id (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    restrictIdealModuleHom hπ ≫ restrictIdealModuleInv hπ = 𝟙 _ := sorry

/-- The inverse and forward comparisons compose to the identity on the kernel ideal sheaf. -/
theorem restrictIdealModuleInv_hom_id (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    restrictIdealModuleInv hπ ≫ restrictIdealModuleHom hπ = 𝟙 _ := sorry

/-- Restriction of scalars of the descended kernel module recovers the kernel ideal sheaf. -/
noncomputable def restrictIdealModuleIso (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    (restrictionAlong π).obj (idealModule hπ) ≅ KernelIdeal.sheaf π where
  hom := restrictIdealModuleHom hπ
  inv := restrictIdealModuleInv hπ
  hom_inv_id := restrictIdealModuleHom_inv_id hπ
  inv_hom_id := restrictIdealModuleInv_hom_id hπ

/-- After square-zero descent, the restriction tensor comparison for the kernel module and quotient
module is an isomorphism. -/
theorem tensorComparison_ideal_isIso (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    IsIso (Restriction.tensorComparison π (idealModule hπ) E.quot) := sorry

/-- The canonical target-ring-linear infinitesimal map associated to a mixed-scalar extension. -/
noncomputable def infMap (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] (E : Extension π) :
    moduleTensor (idealModule hπ) E.quot ⟶ E.kernel :=
  have := tensorComparison_ideal_isIso hπ E
  (restrictHomEquivOfIsLocallySurjective (ringSheafMap π)
      (moduleTensor (idealModule hπ) E.quot) E.kernel).symm
    (inv (Restriction.tensorComparison π (idealModule hπ) E.quot) ≫
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

end FirstOrderThickening
end SheafOfModules.RingedSite
