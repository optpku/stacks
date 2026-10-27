/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatMorphismShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Trivial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Pushout
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Exact

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension

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

/-- The Ext¹ class of the pushout of a prescribed module extension along compatible
thickening and coefficient maps, restricted along the canonical splitting of a complex
of first-order thickenings and identified with the original endpoint modules. -/
noncomputable def pushoutExtClass
    {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪} {π3 : 𝒪3 ⟶ 𝒪}
    [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
    [IsFirstOrderThickening π3]
    (f : Hom π1 π2) (g : Hom π2 π3) (hC : IsComplex f g)
    {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c1 : moduleTensor (ideal π1) F ⟶ K1)
    (c2 : moduleTensor (ideal π2) F ⟶ K2) (κ21 : K2 ⟶ K1)
    (hc12 : CommSq c2
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget f.hom f.comm hπ1.isSquareZero hπ2.isSquareZero) (𝟙 F))
      κ21 c1)
    (E2 : ModuleExtension hπ2.isSquareZero F K2 c2) : Ext F K1 1 :=
  let E1 := pushout f.hom f.comm κ21 hc12 E2
  let σ := canonicalTrivialization f g hC
  let hσ := canonicalTrivialization_isTrivialization f g hC
  let ξ := (E1.shortExact.map_of_exact (restrictionAlong σ)).extClass
  ((Ext.mk₀ (restrictEndpointIso π1 σ hσ F).inv).comp ξ (zero_add 1)).comp
    (Ext.mk₀ (restrictEndpointIso π1 σ hσ K1).hom) (add_zero 1)

variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- For a complex of first-order thickenings and a compatible short exact coefficient
sequence, the connecting map sends the pushed-out extension class obtained from the
canonical splitting to the existence obstruction for the third infinitesimal map. -/
theorem connecting_extClass_eq_obstruction
    {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪} {π3 : 𝒪3 ⟶ 𝒪}
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
    (E2 : ModuleExtension hπ2.isSquareZero F K2 c2) :
    (pushoutExtClass f g hC c1 c2 κ21 hc12 E2).comp hκ.extClass (rfl : 1 + 1 = 2) =
      existenceObstruction π3 F K3 c3 := sorry

end SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension
