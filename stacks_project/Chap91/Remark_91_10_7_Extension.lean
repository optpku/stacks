/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Map
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.Restriction

noncomputable section

universe u v

namespace SheafOfModules.RingedSite
namespace FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section IdealModule

variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [Sheaf.IsLocallySurjective π]

namespace ModuleExtension

variable {hπ : KernelIdeal.IsSquareZero π}
variable {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable {c : moduleTensor (idealModule hπ) F ⟶ K}

/- Assemble a prescribed extension from its middle module, endpoint maps, and defining certificates. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.of :
    ∀ (E : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
    (incl : (restrictionAlong π).obj K ⟶ E)
    (proj : E ⟶ (restrictionAlong π).obj F)
    (zero : incl ≫ proj = 0)
    (shortExact : (ShortComplex.mk incl proj zero).ShortExact)
    (compatible : CompatibleC hπ incl proj c),
    ModuleExtension hπ F K c)

/- The canonical infinitesimal map of an extension recovers the prescribed c. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.infMap_eq :
    ∀ (E : ModuleExtension hπ F K c),
    infMap hπ E.toExtension = c)

/- An extension is a short exact mixed-scalar sequence whose infinitesimal action
recovers the prescribed c. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.spec :
    ∀ (E : ModuleExtension hπ F K c),
    (toShortComplex E).ShortExact ∧ CompatibleC hπ E.incl E.proj c)

end ModuleExtension

end IdealModule

section IdealMap

variable {𝒪 𝒪1 𝒪2 : Sheaf J CommRingCat.{max u v}}
variable {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
variable [Sheaf.IsLocallySurjective π1] [Sheaf.IsLocallySurjective π2]

/-- The induced map of descended ideals, using the canonical kernel comparison. -/
noncomputable abbrev idealMap (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2) :
    idealModule hπ2 ⟶ idealModule hπ1 :=
  KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2

/- The induced kernel map is compatible with the inclusions of ℐᵢ into 𝒪'ᵢ. -/
#check (SheafOfModules.RingedSite.KernelIdeal.IsSquareZero.mapToTarget_comp_ι :
    ∀ (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2),
    (hπ2.targetModuleForgetIso inferInstance).inv ≫
        (SheafOfModules.toSheaf (ringSheaf J 𝒪)).map (KernelIdeal.IsSquareZero.mapToTarget h h_comm hπ1 hπ2) ≫
          (hπ1.targetModuleForgetIso inferInstance).hom ≫
            (SheafOfModules.toSheaf (ringSheaf J 𝒪1)).map (KernelIdeal.ι π1) =
      (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map (KernelIdeal.ι π2) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap h))

end IdealMap

end FirstOrderThickening
end SheafOfModules.RingedSite
