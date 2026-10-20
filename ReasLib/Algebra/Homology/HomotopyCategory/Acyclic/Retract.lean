/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.HomologicalKernel.Retract
public import ReasLib.CategoryTheory.ObjectProperty.Retract.InverseImage

@[expose] public section

/-!
# Retracts of Acyclic Homotopy Complexes

The acyclic subcategory of a homotopy category is definitionally a homological kernel.  This
leaf exposes its retract stability as a named global instance so typeclass search need not unfold
that implementation detail at every use site.
-/

universe v u

open CategoryTheory

namespace HomotopyCategory

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Stacks 05RT: the acyclic subcategory of the homotopy category is stable under retracts. -/
@[stacks 05RT "retract stability of acyclic homotopy complexes"]
instance subcategoryAcyclic_isStableUnderRetracts :
    (subcategoryAcyclic A).IsStableUnderRetracts := sorry


end HomotopyCategory
