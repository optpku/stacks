/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization

/-!
# Reflection of isomorphisms by pretriangulated functors

An exact functor between pretriangulated categories reflects isomorphisms precisely when it
reflects zero objects.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [Preadditive C] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]

/-- An exact shift-compatible functor reflects zero objects if and only if it reflects
isomorphisms. -/
theorem reflectsZero_iff_reflectsIsomorphisms (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] :
    (∀ X : C, IsZero (F.obj X) ↔ IsZero X) ↔ F.ReflectsIsomorphisms := sorry

end CategoryTheory.Functor
