/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Triangulated
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated

@[expose] public section

/-!
# Triangulated Domains of Definition for Pointwise Derived Functors

Mathlib's `Definedness.property` records only existence of the pointwise colimit (or limit).
That predicate is weaker than the essential-constancy notion used by Stacks 05S9, so no
triangulated-domain or triangulated-functor instances are exported for it here.  The source-faithful
05SE API is owned by `Functor.RightDerived.DefinedAt` and `Functor.LeftDerived.DefinedAt`.
The zero-object statements below follow by forgetting essential constancy.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits MorphismProperty
open scoped ZeroObject

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [_root_.CategoryTheory.IsTriangulated D]
  (F : D ⥤ D') (S : MorphismProperty D)

/-- The pointwise right-derived existence property contains zero, by essential constancy. -/
@[stacks 05SE]
theorem Functor.RightDerived.Definedness.property.zero
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    Functor.RightDerived.Definedness.property F S (0 : D) := by
  letI := Functor.RightDerived.DefinedAt.zero (F := F) (S := S)
  exact Functor.RightDerived.DefinedAt.hasPointwise

/-- The pointwise left-derived existence property contains zero, by essential constancy. -/
@[stacks 05SE]
theorem Functor.LeftDerived.Definedness.property.zero
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    Functor.LeftDerived.Definedness.property F S (0 : D) := by
  letI := Functor.LeftDerived.DefinedAt.zero (F := F) (S := S)
  exact Functor.LeftDerived.DefinedAt.hasPointwise

end CategoryTheory
