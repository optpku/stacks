/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated

@[expose] public section

/-!
# Triangulated Domains of Definition for Pointwise Derived Functors

This leaf specializes the general full-subcategory localization API to the object properties
where pointwise derived values are defined.  It provides the zero, triangle, shift, and
localization-factorization interfaces needed by applications without making them depend on the
Chapter 13 presentation.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits Localization MorphismProperty ObjectProperty Pretriangulated
open scoped ZeroObject

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [_root_.CategoryTheory.IsTriangulated D]
  (F : D ⥤ D') (S : MorphismProperty D)

/-- the right-derived-defined object property contains the zero object in a
triangulated localization situation. -/
@[stacks 05SE]
theorem Functor.RightDerived.Definedness.property.zero
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    Functor.RightDerived.Definedness.property F S (0 : D) := sorry

/-- the left-derived-defined object property contains the zero object in a
triangulated localization situation. -/
@[stacks 05SE]
theorem Functor.LeftDerived.Definedness.property.zero
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    Functor.LeftDerived.Definedness.property F S (0 : D) := sorry

/-- the full subcategory on which the pointwise right-derived functor is defined
is triangulated. -/
@[stacks 05SE]
instance Functor.RightDerived.Definedness.property.isTriangulated
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.RightDerived.Definedness.property F S).IsTriangulated := sorry

/-- the full subcategory on which the pointwise left-derived functor is defined
is triangulated. -/
@[stacks 05SE]
instance Functor.LeftDerived.Definedness.property.isTriangulated
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.LeftDerived.Definedness.property F S).IsTriangulated := sorry

/-- the right-derived functor on its domain of definition is triangulated. -/
@[stacks 05SE]
instance Functor.RightDerived.Definedness.functor.isTriangulated
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.RightDerived.Definedness.functor F S).IsTriangulated := sorry

/-- the localized right-derived factorization is triangulated. -/
@[stacks 05SE]
instance Functor.RightDerived.Definedness.localizationFactorization.isTriangulated
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.RightDerived.Definedness.localizationFactorization F S).IsTriangulated := sorry

/-- the left-derived functor on its domain of definition is triangulated. -/
@[stacks 05SE]
instance Functor.LeftDerived.Definedness.functor.isTriangulated
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.LeftDerived.Definedness.functor F S).IsTriangulated := sorry

/-- the localized left-derived factorization is triangulated. -/
@[stacks 05SE]
instance Functor.LeftDerived.Definedness.localizationFactorization.isTriangulated
    [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [_root_.CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.LeftDerived.Definedness.localizationFactorization F S).IsTriangulated := sorry


end CategoryTheory
