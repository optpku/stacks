/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Exactness.Faithful

/-!
# Reflection of monomorphisms and epimorphisms

Exact functors of abelian categories that reflect zero objects also reflect monomorphisms and
epimorphisms.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/-- An exact functor between abelian categories that reflects zero objects reflects
monomorphisms. -/
theorem reflectsMonomorphisms_of_exact_of_kernel_le_isZero
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (F : A ⥤ B) (h_exact : exactFunctor A B F) (h_zero : F.kernel ≤ IsZero) :
    F.ReflectsMonomorphisms := sorry

/-- An exact functor between abelian categories that reflects zero objects reflects
epimorphisms. -/
theorem reflectsEpimorphisms_of_exact_of_kernel_le_isZero
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (F : A ⥤ B) (h_exact : exactFunctor A B F) (h_zero : F.kernel ≤ IsZero) :
    F.ReflectsEpimorphisms := sorry

end CategoryTheory.Functor
