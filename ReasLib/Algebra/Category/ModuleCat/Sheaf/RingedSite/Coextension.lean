/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

/-!
# Coextension of scalars for sheaves of modules

This module constructs the right adjoint to same-site restriction of scalars for sheaves of
modules and records exactness of restriction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Same-site restriction of scalars for sheaves of modules has a right adjoint. -/
@[stacks 0A6F "restriction has a right adjoint"]
noncomputable instance restrictionAlong_isLeftAdjoint
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    (restrictionAlong α).IsLeftAdjoint := sorry

/-- The same-site coextension functor `Hom_𝒪(𝒪', -)`, realized as the canonical right adjoint of
restriction of scalars along `α`. -/
abbrev coextendAlong
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪' :=
  (restrictionAlong α).rightAdjoint

/-- Restriction of scalars along `α` is canonically left adjoint to coextension along `α`. -/
@[stacks 0A6F]
noncomputable def restrictionCoextendAdj
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    restrictionAlong α ⊣ coextendAlong α :=
  Adjunction.ofIsLeftAdjoint (restrictionAlong α)

variable [HasWeakSheafify J AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

/-- Same-site restriction of scalars is exact on sheaves of modules. -/
theorem restrictionAlong_exact
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    exactFunctor
      (ringedSiteModuleCategory J 𝒪')
      (ringedSiteModuleCategory J 𝒪)
      (restrictionAlong α) := sorry

end SheafOfModules.RingedSite
