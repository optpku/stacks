/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening

/-!
# Kernel of the extension-restriction unit on a first-order thickening

On a same-site first-order thickening π : 𝒪' ⟶ 𝒪, the 𝒪'-module ℐ M is the kernel of the
adjunction unit M ⟶ i_* i^* M, and the 𝒪-module ℐ M is the extension of scalars of that
kernel.
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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} (π : 𝒪' ⟶ 𝒪)
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]

/-- The adjunction unit M ⟶ i_* i^* M of extension and restriction of scalars along π. -/
abbrev extendRestrictUnit (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    M ⟶ (restrictionAlong π).obj
      ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)).unit.app M

/-- The 𝒪'-module ℐ M, as the kernel of the extension-restriction unit of M. -/
def idealMulO' (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪' :=
  kernel (extendRestrictUnit π M)

/-- The 𝒪-module ℐ M, obtained by extending scalars of `idealMulO' π M` along π. -/
def idealMul (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪 :=
  (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj (idealMulO' π M)

/-- The short complex ℐ M ⟶ M ⟶ i_* i^* M of 𝒪'-modules associated to the unit of M. -/
def unitShortComplex (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :=
  ShortComplex.mk (kernel.ι (extendRestrictUnit π M)) (extendRestrictUnit π M)
    (kernel.condition (extendRestrictUnit π M))

/-- The unit sequence 0 ⟶ ℐ M ⟶ M ⟶ i_* i^* M ⟶ 0 is short exact as 𝒪'-modules. -/
theorem unitShortComplex_shortExact
    (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    (unitShortComplex π M).ShortExact := sorry

/-- Extension of scalars along π identifies Hom_{𝒪'}(ℱ', ℐ 𝒢') with Hom_𝒪(ℱ, ℐ 𝒢'). -/
theorem map_kernel_bijective
    (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :
    Function.Bijective fun β : F' ⟶ idealMulO' π G' ↦
      (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map β :=
  sorry

end SheafOfModules.RingedSite.FirstOrderThickening
