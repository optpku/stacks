/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.UnivLE

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe u v r w
namespace CategoryTheory.GrothendieckTopology
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type r) [Ring R] [UnivLE.{max u v, w}]

/-- Forgetting module structure preserves the filtered colimits indexed by opposite covers. -/
instance moduleForgetPreservesCoverColimits (X : C) :
    PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (ModuleCat.{w} R)) := sorry

/-- Module-valued presheaves on a universe-bounded site admit the canonical plus-plus sheafification. -/
noncomputable instance moduleHasSheafify : HasSheafify J (ModuleCat.{w} R) :=
  HasSheafify.mk' J (ModuleCat.{w} R) (plusPlusAdjunction J (ModuleCat.{w} R))

end CategoryTheory.GrothendieckTopology
