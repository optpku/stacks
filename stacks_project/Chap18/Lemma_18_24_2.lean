/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
import StacksCheckRecall

/-!
# Lemma 18.24.2

The finite-type kernel theorem is owned at the generic
SheafOfModules.IsFinitePresentation level.
-/

@[expose] public section

open CategoryTheory Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (O : Sheaf J CommRingCat.{max u v})
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective
  AddCommGrpCat.{max u v}]
variable {G F : ringedSiteModuleCategory J O} (θ : G ⟶ F)
variable [Epi θ] [G.IsFiniteType] [F.IsFinitePresentation]

/- Lemma 18.24.2 (082T): the kernel of a surjection from a finite-type module sheaf to a finitely
presented module sheaf is finite type. -/
@[stacks 082T]
#check
  (IsFinitePresentation.kernel_of_epi θ :
    (kernel θ).IsFiniteType)

end SheafOfModules
