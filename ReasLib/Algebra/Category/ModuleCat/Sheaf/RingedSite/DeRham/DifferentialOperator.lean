/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DeRham.DifferentialOperator
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator.Sheafification
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential-operator order of ringed-site de Rham differentials

The presheaf first-order bound descends through module sheafification.  This
leaf isolates that property from the data-bearing construction of the de Rham
complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DeRham

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- Lemma 17.30.3 (0G3Y): every relative de Rham differential on a
ringed site is a differential operator of order at most one. -/
@[stacks 0G3Y]
theorem d_isOrderOne (φ : O₁ ⟶ O₂) (p : ℕ) :
    IsDifferentialOperatorOfOrder φ (d φ p) 1 := sorry

end SheafOfModules.RingedSite.DeRham
