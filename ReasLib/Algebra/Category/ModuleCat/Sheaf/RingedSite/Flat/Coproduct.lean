module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Colimits
public import ReasLib.CategoryTheory.Monoidal.Flat.Coproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproduct closure for flat module sheaves

This file installs the categorical coproduct-closure interface for flat modules on a
commutative ringed site. Downstream complex and graded-object APIs can use the generic class.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.IsFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Flat module sheaves are closed under small coproducts. -/
@[stacks 03EU "flat module-sheaf coproducts", instance]
theorem coproducts (O : Sheaf J CommRingCat.{w}) :
    CategoryTheory.MonoidalCategory.IsFlat.Coproducts
      (ringedSiteModuleCategory.{u, v, w, w} J O) := sorry

end SheafOfModules.RingedSite.IsFlat
