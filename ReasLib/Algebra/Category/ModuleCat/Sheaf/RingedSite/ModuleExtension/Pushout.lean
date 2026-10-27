/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Pushout
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension

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

namespace ModuleExtension

/-- Push an extension with prescribed infinitesimal map along compatible maps of the presentation
and kernel coefficients, using the canonical mixed-scalar pushout. -/
noncomputable def pushout (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) : ModuleExtension hπ1 F K1 c1 := by
  have hc' : CommSq (infMap hπ2 F'2.toExtension)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 F))
      k c1 := by
    change CommSq (infMap hπ2 F'2.toExtension)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 F)) k c1
    rw [F'2.infMap_eq]
    exact hc
  exact
    { module := (Extension.pushout F'2.toExtension h h_comm k hc').middle
      incl := (Extension.pushout F'2.toExtension h h_comm k hc').ι
      proj := (Extension.pushout F'2.toExtension h h_comm k hc').p
      zero := (Extension.pushout F'2.toExtension h h_comm k hc').zero
      shortExact := (Extension.pushout F'2.toExtension h h_comm k hc').shortExact
      compatible := Extension.pushout_restrictC_spec F'2.toExtension h h_comm k hc' }

/-- The middle module of the pushout extension with prescribed infinitesimal map. -/
noncomputable abbrev pushoutSheaf (h_comm : h ≫ π1 = π2) (k : K2 ⟶ K1)
    (hc : CommSq c2 (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) (𝟙 F)) k c1)
    (F'2 : ModuleExtension hπ2 F K2 c2) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪1 :=
  (pushout h h_comm k hc F'2).module

end ModuleExtension

end SheafOfModules.RingedSite.FirstOrderThickening
