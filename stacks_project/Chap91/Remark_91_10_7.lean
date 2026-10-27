/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Pushout
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Pushout
public import stacks_project.Chap91.Remark_91_10_7_Extension
import StacksCheckRecall

/-!
# Functoriality of extensions along morphisms of first-order thickenings

The canonical changed-scalar pushout is presented here with prescribed kernel and quotient
modules, for compatibility with the indexed extension presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 𝒪1 𝒪2 : Sheaf J CommRingCat.{max u v}}
variable {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
variable [Sheaf.IsLocallySurjective π1] [Sheaf.IsLocallySurjective π2]
variable {hπ1 : KernelIdeal.IsSquareZero π1} {hπ2 : KernelIdeal.IsSquareZero π2}
variable {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable {c1 : moduleTensor (idealModule hπ1) F ⟶ K1}
variable {c2 : moduleTensor (idealModule hπ2) F ⟶ K2}
variable (h : 𝒪2 ⟶ 𝒪1)

section CanonicalPushout

variable (E₂ : Extension π2) (h_comm : h ≫ π1 = π2)
variable (c₁ : moduleTensor (idealModule hπ1) E₂.quot ⟶ K1) (k : E₂.kernel ⟶ K1)
variable (hc : CommSq (infMap hπ2 E₂)
  (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 E₂.quot)) k c₁)

/- Remark 91.10.7: after identifying the underlying topoi, a morphism of first-order thickenings
induces a map of their ideal modules. A commuting square of the prescribed infinitesimal maps
and a map of kernel coefficients canonically sends an extension to its additive-sheaf pushout,
with the target thickening's module structure, the same quotient, and the prescribed kernel
and infinitesimal map. The scalar action uses a local lift of π₁(a) through π₂ and the correction
c₁((a - h(b)) ⊗ proj(s')), where π₂(b) = π₁(a).
-/
@[stacks 08MJ] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.Extension.pushout_spec E₂ h h_comm k hc :
    (Extension.pushout E₂ h h_comm k hc).kernel = K1 ∧
      (Extension.pushout E₂ h h_comm k hc).quot = E₂.quot ∧
      (shortComplex (Extension.pushout E₂ h h_comm k hc)).ShortExact ∧
      infMap hπ1 (Extension.pushout E₂ h h_comm k hc) = c₁ ∧
      IsPushout (Extension.inclUnderlying E₂) (Extension.kernelUnderlying k)
        (Extension.pushoutInlSheaf E₂ k) (Extension.pushoutInrSheaf E₂ k))

end CanonicalPushout

end SheafOfModules.RingedSite.FirstOrderThickening
