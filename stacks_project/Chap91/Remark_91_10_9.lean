module

public import stacks_project.Chap91.Lemma_91_10_4_Obstruction
public import stacks_project.Chap91.Remark_91_10_7
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction.Naturality
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of existence obstructions along morphisms of first-order thickenings

After identifying underlying topoi, a morphism of first-order thickenings of (Sh(C), 𝒪)
induces an 𝒪-module map of kernel ideals, and Ext-postcomposition in the kernel variable
sends the existence obstruction of Lemma 91.10.4 on the source thickening to the obstruction
on the target.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

universe u v w

/- Remark 91.10.9: after identifying underlying topoi, the source morphism of ringed topoi
from the first thickening to the second gives h.hom : 𝒪2 ⟶ 𝒪1 with h.hom ≫ π1 = π2,
and hence h.idealMap : ℐ2 ⟶ ℐ1. For the fixed module ℱ and compatible k : 𝒦2 ⟶ 𝒦1,
Ext² coefficient postcomposition sends the canonical existenceObstruction for π2 to that
for π1. -/
@[stacks 0CYC] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.obstruction_postcomp :
    ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
      [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
      [HasWeakSheafify J CommRingCat.{max u v}]
      [J.WEqualsLocallyBijective CommRingCat.{max u v}]
      [HasWeakSheafify J AddCommGrpCat.{max u v}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
      [HasSheafify J AddCommGrpCat.{max u v}]
      {𝒪 𝒪1 𝒪2 : Sheaf J CommRingCat.{max u v}}
      [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
      [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]
      {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
      [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
      [(SheafOfModules.restrictScalars (ringSheafMap π1)).IsRightAdjoint]
      [(SheafOfModules.restrictScalars (ringSheafMap π2)).IsRightAdjoint]
      [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪1)]
      [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪2)]
      {F K1 K2 : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
      {c1 : moduleTensor (ideal π1) F ⟶ K1}
      {c2 : moduleTensor (ideal π2) F ⟶ K2}
      (h : FirstOrderThickening.Hom π1 π2) (k : K2 ⟶ K1)
      (hc : CommSq c2 (moduleTensorMap h.idealMap (𝟙 F)) k c1),
      (CategoryTheory.Abelian.Ext.mk₀ k).postcomp F (add_zero 2)
          (SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.existenceObstruction
            π2 F K2 c2) =
        SheafOfModules.RingedSite.FirstOrderThickening.ModuleExtension.existenceObstruction
          π1 F K1 c1)
