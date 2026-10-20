/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinal-bounded local generation of sheaves of modules

This file records the existence of local generating sections whose indexing
types have bounded cardinality.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A sheaf of modules is `κ`-generated if it admits local generator data whose family of
generating sections on every chart has cardinality at most `κ`. -/
def IsKappaGenerated (M : SheafOfModules.{w} R) (κ : Cardinal.{w}) : Prop :=
  ∃ q : M.LocalGeneratorsData.{u},
    ∀ i : q.I, Cardinal.mk (q.generators i).I ≤ κ

/-- Characterization of cardinal-bounded local generation by local generator data. -/
theorem isKappaGenerated_iff (M : SheafOfModules.{w} R) (κ : Cardinal.{w}) :
    M.IsKappaGenerated κ ↔
      ∃ q : M.LocalGeneratorsData.{u},
        ∀ i : q.I, Cardinal.mk (q.generators i).I ≤ κ :=
  Iff.rfl

end SheafOfModules
