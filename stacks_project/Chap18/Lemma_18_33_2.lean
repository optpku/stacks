/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
import StacksCheckRecall

/-! # Lemma 18.33.2 compatibility entry point -/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation SheafOfModules.RingedSite

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}} (phi : O₁ ⟶ O₂)
variable (F : ringedSiteModuleCategory J O₂) (D : Der[phi ; F])

/- Lemma 18.33.2 (04BL): `Ω(phi)` represents relative derivations. -/
@[stacks 04BL]
#check (relativeDifferentials_representsDerivations phi F D :
  ∃! f : Ω(phi) ⟶ F, (relativeDifferential phi).postcomp f.val = D)

#check relativeDifferentialDesc phi D
#check relativeDifferentialDesc_fac phi D
#check relativeDifferential_postcomp_injective phi
