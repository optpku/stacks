/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.IntMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.CategoryTheory.GradedObject.Instances
public import ReasLib.CategoryTheory.GradedObject.Monoidal.Closed
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed integer-graded module sheaves on a ringed site

The convolution tensor category of integer-graded module sheaves has the canonical product-valued
internal Hom.  This file registers the ringed-site specialization of the generic graded closed
construction, so downstream relative tensor/Hom APIs need no local instance setup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.IntGraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The canonical closed structure on integer-graded module sheaves over a ringed site. -/
@[stacks 0FR6 "closed integer-graded module sheaves", instance_reducible]
noncomputable instance monoidalClosed :
    MonoidalClosed (GradedObject ℤ (ringedSiteModuleCategory J O)) :=
  CategoryTheory.GradedObject.InternalHom.monoidalClosed

#synth MonoidalClosed
  (GradedObject ℤ (ringedSiteModuleCategory J O))
#synth BraidedCategory
  (GradedObject ℤ (ringedSiteModuleCategory J O))
#synth HasEqualizers
  (GradedObject ℤ (ringedSiteModuleCategory J O))
#synth HasCoequalizers
  (GradedObject ℤ (ringedSiteModuleCategory J O))
#synth ∀ X : GradedObject ℤ (ringedSiteModuleCategory J O),
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)
#synth ∀ X : GradedObject ℤ (ringedSiteModuleCategory J O),
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)

end SheafOfModules.RingedSite.IntGraded

end
