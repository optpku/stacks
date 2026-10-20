/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Lattice operations on weak Serre classes

Weak Serre object properties are closed under arbitrary intersections.  This is the natural
owner-level operation needed when a property is characterized by a family of exact comparison
maps.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.ObjectProperty.IsWeakSerreClass

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- An arbitrary intersection of weak Serre object properties is a weak Serre object property. -/
instance iInf {ι : Type w} (P : ι → ObjectProperty A)
    [∀ i, IsWeakSerreClass (P i)] :
    IsWeakSerreClass (iInf P) := sorry

end CategoryTheory.ObjectProperty.IsWeakSerreClass
