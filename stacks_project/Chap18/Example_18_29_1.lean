/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Duality
import StacksCheckRecall

/-!
# Example 18.29.1

Compatibility facade for the canonical dual of a locally finite-free retract.  The closed
monoidal construction is owned generically by `CategoryTheory.MonoidalClosed`; the local
ringed-site criterion is owned by `FiniteFreeRetract.IsLocal`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable (M : ringedSiteModuleCategory J 𝒪)
variable [FiniteFreeRetract.IsLocal M]

/- Example 18.29.1 (0FNY): the canonical tensor/internal-Hom comparison. -/
@[stacks 0FNY "canonical comparison"]
#check (CategoryTheory.MonoidalClosed.tensorIhomUnitToEnd M :
  M ⊗ (ihom M).obj (𝟙_ (ringedSiteModuleCategory J 𝒪)) ⟶ (ihom M).obj M)

/- Example 18.29.1 (0FNY): local finite-free retracts make the comparison invertible. -/
@[stacks 0FNY "local finite-free retract criterion"]
#check (FiniteFreeRetract.IsLocal.isIso_tensorIhomUnitToEnd M :
  IsIso (CategoryTheory.MonoidalClosed.tensorIhomUnitToEnd M))

/- Example 18.29.1 (0FNY): the resulting internal Hom into the structure module is a left
dual. -/
@[stacks 0FNY "canonical left dual"]
#check (CategoryTheory.MonoidalClosed.ihomUnitExactPairing M :
  ExactPairing ((ihom M).obj (𝟙_ (ringedSiteModuleCategory J 𝒪))) M)

end SheafOfModules.RingedSite
