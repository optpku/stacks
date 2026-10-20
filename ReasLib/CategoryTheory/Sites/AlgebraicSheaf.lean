/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Sheaves valued in algebraic categories

This file gives ergonomic specializations of mathlib's general criterion
`Presheaf.isSheaf_iff_isSheaf_forget` for common algebraic categories. The general
criterion, rather than an ad hoc `Presieve.IsSheaf` predicate, is the canonical model
for category-valued sheaves.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace Presheaf

/-- Specialization: a presheaf of commutative rings is a sheaf iff its underlying
presheaf of sets is. -/
theorem isSheaf_commRingCat_iff (F : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    IsSheaf J F ↔ IsSheaf J (F ⋙ forget CommRingCat.{max u v}) := sorry

/-- Specialization: a presheaf of abelian groups is a sheaf iff its underlying
presheaf of sets is. -/
theorem isSheaf_addCommGrpCat_iff (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    IsSheaf J F ↔ IsSheaf J (F ⋙ forget AddCommGrpCat.{max u v}) := sorry

end Presheaf

end CategoryTheory
