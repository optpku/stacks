/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.Algebra.Category.ModuleCat.Grothendieck
public import ReasLib.CategoryTheory.Sites.ModuleSheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe u v r w
namespace CategoryTheory.ModuleSheaf

/-- Module-valued sheaves on a universe-bounded site form a Grothendieck abelian category
when the ring is small in the module universe. -/
instance isGrothendieckAbelian {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type r) [Ring R]
    [UnivLE.{max u v, w}] [Small.{w} R] :
    IsGrothendieckAbelian.{w} (Sheaf J (ModuleCat.{w} R)) := sorry

end CategoryTheory.ModuleSheaf
