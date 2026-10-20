/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
import StacksCheckRecall

/-! # Definition 18.33.3 compatibility entry point -/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}} (phi : O₁ ⟶ O₂)

/- Definition 18.33.3 (04BN): the sheaf of relative differentials is the
canonical site-generic owner `Ω(phi)`. -/
@[stacks 04BN]
#check (relativeDifferentials phi : ringedSiteModuleCategory J O₂)

#check relativeDifferentials_def phi
#check relativeDifferential phi
