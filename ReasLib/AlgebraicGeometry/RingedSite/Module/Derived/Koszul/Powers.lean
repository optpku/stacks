/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul.Powers
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import Mathlib.CategoryTheory.Functor.OfSequence

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.Koszul

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- The derived object represented by the ordinary Koszul complex on the `(n + 1)`st powers. -/
noncomputable def poweredKoszulChainDerived
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    RingedSiteDerived J O :=
  (@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
    (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).obj (poweredKoszulChainStage f n)

/-- The ordinary powered Koszul derived stage is the localization of its explicit complex. -/
theorem poweredKoszulChainDerived_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainDerived f n =
      ((@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
    (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))) :
        CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ RingedSiteDerived J O).obj
        (poweredKoszulChainStage f n) := sorry

/-- The adjacent derived transition is induced by the concrete diagonal powered-Koszul map. -/
noncomputable def poweredKoszulChainDerivedStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainDerived f (n + 1) ⟶ poweredKoszulChainDerived f n :=
  (@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
    (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).map (poweredKoszulChainStep f n)

/-- The derived successor transition is the image of the explicit cochain transition. -/
theorem poweredKoszulChainDerivedStep_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainDerivedStep f n =
      (@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
    (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).map (poweredKoszulChainStep f n) := sorry

/-- The derived powered-Koszul inverse system, including its canonical transition maps. -/
noncomputable def poweredKoszulChainSystem
    {r : ℕ} (f : Fin r → (unitModule J O).sections) :
    ℕᵒᵖ ⥤ RingedSiteDerived J O :=
  Functor.ofOpSequence (poweredKoszulChainDerivedStep f)

/-- Object `n` of the ordinary powered-Koszul inverse system is its `(n + 1)`st-power stage. -/
theorem poweredKoszulChainSystem_obj
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredKoszulChainSystem f).obj (Opposite.op n) =
      poweredKoszulChainDerived f n := sorry

/-- The successor map of the ordinary inverse system is its explicit derived Koszul map. -/
theorem poweredKoszulChainSystem_map_succ
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredKoszulChainSystem f).map (homOfLE (Nat.le_succ n)).op =
      poweredKoszulChainDerivedStep f n := sorry

end SheafOfModules.RingedSite.Koszul
