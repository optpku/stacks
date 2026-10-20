/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Galois.Action
public import Mathlib.CategoryTheory.Galois.Topology
import StacksCheckRecall

@[expose] public section

universe u v w

open CategoryTheory

/- 58.3.5.1: With Aut(F) carrying its canonical topology, a finite-valued functor
`F : C ⥤ FintypeCat` induces `C ⟶` finite Aut(F)-sets by `X ↦ F.obj X` with the
induced Aut(F)-action; that action is continuous. -/
@[stacks 0BMX] #check (CategoryTheory.PreGaloisCategory.finiteActionFunctor :
  {C : Type u} → [Category.{v} C] → (F : C ⥤ FintypeCat.{w}) →
    C ⥤ Action FintypeCat.{w} (Aut F))

#check PreGaloisCategory.finiteActionFunctor_comp_forget₂_eq
#check PreGaloisCategory.functorToAction_comp_forget₂_eq
#check PreGaloisCategory.continuousSMul_aut_fiber
