/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Connecting
import StacksCheckRecall

/-!
# Connecting map of a kernel SES versus the existence obstruction

Along a complex of first-order thickenings of a ringed topos, an 08MB extension on the
middle thickening pushes out to the first thickening. Its Ext¹ class, formed using the
canonical trivialization, is sent by the connecting map of a kernel short exact sequence
to the existence obstruction on the last thickening.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪 𝒪1 𝒪2 𝒪3 : Sheaf J CommRingCat.{max u v}}
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/- Remark 91.10.11: Let (Sh(C), 𝒪) be a ringed topos and ℱ an 𝒪-module. After
identifying the underlying topoi, the thickening maps are ring-sheaf maps
πᵢ : 𝒪'ᵢ ⟶ 𝒪. A complex of first-order thickenings is packaged as morphisms
f : Hom π1 π2 and g : Hom π2 π3 with IsComplex f g. Let (𝒦ᵢ, cᵢ) be 𝒪-modules
and maps cᵢ : ℐᵢ ⊗ ℱ ⟶ 𝒦ᵢ, and let 0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0 be a short exact
sequence of 𝒪-modules making the two infinitesimal-map squares commute. Given
an 08MB extension ℱ'₂ of ℱ by 𝒦₂ with c_{ℱ'₂} = c₂, the 91.10.7 pushout ℱ'₁
has Ext class ξ along the canonical trivialization of π1, and the connecting
map ∂ : Ext ℱ 𝒦₁ 1 ⟶ Ext ℱ 𝒦₃ 2 of the kernel sequence sends ξ to the
existence obstruction o(ℱ, 𝒦₃, c₃). -/
@[stacks 08MM] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.connecting_extClass_eq_obstruction :
    ∀ {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪} {π3 : 𝒪3 ⟶ 𝒪}
    [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
    [hπ3 : IsFirstOrderThickening π3]
    (f : Hom π1 π2) (g : Hom π2 π3) (hC : IsComplex f g)
    [(SheafOfModules.restrictScalars (ringSheafMap π3)).IsRightAdjoint]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪3)]
    {F K1 K2 K3 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c1 : moduleTensor (ideal π1) F ⟶ K1)
    (c2 : moduleTensor (ideal π2) F ⟶ K2)
    (c3 : moduleTensor (ideal π3) F ⟶ K3)
    (κ32 : K3 ⟶ K2) (κ21 : K2 ⟶ K1) (w : κ32 ≫ κ21 = 0)
    (hκ : (ShortComplex.mk κ32 κ21 w).ShortExact)
    (hc12 : CommSq c2
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget f.hom f.comm hπ1.isSquareZero hπ2.isSquareZero) (𝟙 F))
      κ21 c1)
    (hc23 : CommSq c3
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget g.hom g.comm hπ2.isSquareZero hπ3.isSquareZero) (𝟙 F))
      κ32 c2)
    (E2 : ModuleExtension hπ2.isSquareZero F K2 c2),
    (pushoutExtClass f g hC c1 c2 κ21 hc12 E2).comp hκ.extClass (rfl : 1 + 1 = 2) =
      existenceObstruction π3 F K3 c3)

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
