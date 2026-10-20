/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Triangulated
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.IdentityDenominator
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Triangle.Distinguished
public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Biproducts of Source-Defined Derived Values

The split distinguished triangle attached to a binary biproduct turns the triangulated
two-out-of-three API into a reusable closure operation for source-defined derived values.  The
comparison morphisms of the resulting pointwise values are recorded separately, so applications
can use the source-definedness and value-level APIs independently.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits MorphismProperty Pretriangulated

/-- Stacks 05SD (1): right-derived source-definedness at two summands implies source-definedness
at their binary biproduct. -/
@[stacks 05SD "right source-definedness on a biproduct"]
theorem Functor.RightDerived.DefinedAt.of_biprod
    {D : Type u₁} {D' : Type u₂}
    [Category.{v₁} D] [Category.{v₂} D']
    [HasZeroObject D] [HasZeroObject D']
    [HasShift D ℤ] [HasShift D' ℤ]
    [Preadditive D] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D] [Pretriangulated D']
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    {F : D ⥤ D'} [F.CommShift ℤ] [F.IsTriangulated]
    {S : MorphismProperty D} [IsSaturatedMultiplicativeSystem S]
    [S.IsCompatibleWithTriangulation] {X Y : D}
    [Functor.RightDerived.DefinedAt F S X] [Functor.RightDerived.DefinedAt F S Y] :
    Functor.RightDerived.DefinedAt F S (X ⊞ Y) := sorry

/-- The biproduct closure is available to typeclass search for source-defined right-derived values.
-/
@[stacks 05SD "right source-definedness biproduct instance"]
instance Functor.RightDerived.DefinedAt.biprod
    {D : Type u₁} {D' : Type u₂}
    [Category.{v₁} D] [Category.{v₂} D']
    [HasZeroObject D] [HasZeroObject D']
    [HasShift D ℤ] [HasShift D' ℤ]
    [Preadditive D] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D] [Pretriangulated D']
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    {F : D ⥤ D'} [F.CommShift ℤ] [F.IsTriangulated]
    {S : MorphismProperty D} [IsSaturatedMultiplicativeSystem S]
    [S.IsCompatibleWithTriangulation] {X Y : D}
    [Functor.RightDerived.DefinedAt F S X] [Functor.RightDerived.DefinedAt F S Y] :
    Functor.RightDerived.DefinedAt F S (X ⊞ Y) := sorry

/-- Stacks 05SD (5): left-derived source-definedness at two summands implies source-definedness
at their binary biproduct. -/
@[stacks 05SD "left source-definedness on a biproduct"]
theorem Functor.LeftDerived.DefinedAt.of_biprod
    {D : Type u₁} {D' : Type u₂}
    [Category.{v₁} D] [Category.{v₂} D']
    [HasZeroObject D] [HasZeroObject D']
    [HasShift D ℤ] [HasShift D' ℤ]
    [Preadditive D] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D] [Pretriangulated D']
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    {F : D ⥤ D'} [F.CommShift ℤ] [F.IsTriangulated]
    {S : MorphismProperty D} [IsSaturatedMultiplicativeSystem S]
    [S.IsCompatibleWithTriangulation] {X Y : D}
    [Functor.LeftDerived.DefinedAt F S X] [Functor.LeftDerived.DefinedAt F S Y] :
    Functor.LeftDerived.DefinedAt F S (X ⊞ Y) := sorry

/-- The biproduct closure is available to typeclass search for source-defined left-derived values.
-/
@[stacks 05SD "left source-definedness biproduct instance"]
instance Functor.LeftDerived.DefinedAt.biprod
    {D : Type u₁} {D' : Type u₂}
    [Category.{v₁} D] [Category.{v₂} D']
    [HasZeroObject D] [HasZeroObject D']
    [HasShift D ℤ] [HasShift D' ℤ]
    [Preadditive D] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D] [Pretriangulated D']
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    {F : D ⥤ D'} [F.CommShift ℤ] [F.IsTriangulated]
    {S : MorphismProperty D} [IsSaturatedMultiplicativeSystem S]
    [S.IsCompatibleWithTriangulation] {X Y : D}
    [Functor.LeftDerived.DefinedAt F S X] [Functor.LeftDerived.DefinedAt F S Y] :
    Functor.LeftDerived.DefinedAt F S (X ⊞ Y) := sorry

/-- Stacks 05SD (4): the canonical right-derived value map from the biproduct of the two
pointwise values to the value of the biproduct is an isomorphism. -/
@[stacks 05SD "right-derived biproduct comparison"]
theorem Functor.RightDerived.Biproduct.descIsIso
    {D : Type u₁} {D' : Type u₂}
    [Category.{v₁} D] [Category.{v₂} D']
    [HasZeroObject D] [HasZeroObject D']
    [HasShift D ℤ] [HasShift D' ℤ]
    [Preadditive D] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D] [Pretriangulated D']
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    {F : D ⥤ D'} [F.CommShift ℤ] [F.IsTriangulated]
    {S : MorphismProperty D} [IsSaturatedMultiplicativeSystem S]
    [S.IsCompatibleWithTriangulation] {X Y : D}
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S (X ⊞ Y)] :
    IsIso
      (biprod.desc
        (CategoryTheory.Functor.RightDerived.Value.map F S (biprod.inl : X ⟶ X ⊞ Y))
        (CategoryTheory.Functor.RightDerived.Value.map F S (biprod.inr : Y ⟶ X ⊞ Y))) := sorry

/-- Stacks 05SD (8): the canonical left-derived value map from the biproduct of the two
pointwise values to the value of the biproduct is an isomorphism. -/
@[stacks 05SD "left-derived biproduct comparison"]
theorem Functor.LeftDerived.Biproduct.descIsIso
    {D : Type u₁} {D' : Type u₂}
    [Category.{v₁} D] [Category.{v₂} D']
    [HasZeroObject D] [HasZeroObject D']
    [HasShift D ℤ] [HasShift D' ℤ]
    [Preadditive D] [Preadditive D']
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D] [Pretriangulated D']
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    {F : D ⥤ D'} [F.CommShift ℤ] [F.IsTriangulated]
    {S : MorphismProperty D} [IsSaturatedMultiplicativeSystem S]
    [S.IsCompatibleWithTriangulation] {X Y : D}
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [F.HasPointwiseLeftDerivedFunctorAt S (X ⊞ Y)] :
    IsIso
      (biprod.desc
        (CategoryTheory.Functor.LeftDerived.Value.map F S (biprod.inl : X ⟶ X ⊞ Y))
        (CategoryTheory.Functor.LeftDerived.Value.map F S (biprod.inr : Y ⟶ X ⊞ Y))) := sorry

end CategoryTheory
