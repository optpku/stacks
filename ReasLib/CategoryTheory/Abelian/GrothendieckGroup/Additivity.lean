/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Additivity in Abelian Grothendieck Groups

This file collects representation-independent consequences of the short-exact relations defining
the Grothendieck group of an abelian category.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe u v

namespace CategoryTheory.AbelianK0

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The zero object has zero class in the Grothendieck group. -/
@[simp]
theorem of_zero : K₀[(0 : A)] = 0 := sorry

/-- Isomorphic objects have the same class in the Grothendieck group. -/
theorem of_iso {X Y : A} (e : X ≅ Y) : K₀[X] = K₀[Y] := sorry

/-- The class of a binary biproduct is the sum of the classes of its summands. -/
theorem of_biprod (X Y : A) : K₀[X ⊞ Y] = K₀[X] + K₀[Y] := sorry

/-- Every Grothendieck-group element is a difference of two object classes. -/
theorem exists_eq_sub (x : AbelianK0 A) :
    ∃ X Y : A, x = K₀[X] - K₀[Y] := sorry

/-- The target-source class difference of a morphism is the cokernel-kernel class difference. -/
theorem sub_eq_cokernel_sub_kernel {X Y : A} (f : X ⟶ Y) :
    K₀[Y] - K₀[X] = K₀[cokernel f] - K₀[kernel f] := sorry

end CategoryTheory.AbelianK0
