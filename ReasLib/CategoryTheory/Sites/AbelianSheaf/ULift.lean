/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TypeSheafification.ULift
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Universe lifts of abelian-group-valued sheaves

The canonical universe-lift functor on additive commutative groups preserves
the sheaf condition for every Grothendieck topology.
-/

@[expose] public section

open CategoryTheory

universe u v w w'

namespace CategoryTheory.GrothendieckTopology

/-- Composition with the canonical universe-lift functor on additive commutative groups
preserves the sheaf condition. -/
noncomputable instance uliftFunctor_hasSheafCompose_addCommGrp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose AddCommGrpCat.uliftFunctor.{w', w} := sorry

end CategoryTheory.GrothendieckTopology
