/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive presheaves

This leaf names the functor category of additive presheaves.  The name is shared by derived
colimits, sheaf cohomology, and underlying-module constructions, so those APIs need not repeat
the raw functor-category expression.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AddCommGrpCat

/-- The category of `AddCommGrpCat`-valued presheaves on `C`. -/
@[stacks 08PF "additive presheaves on a category"]
abbrev Presheaf (C : Type u) [Category.{v} C] :=
  Cᵒᵖ ⥤ AddCommGrpCat.{w}

end AddCommGrpCat
