/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Localization
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Shift
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Triangle.Construction
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem

@[expose] public section

/-!
# Triangulated Essential-Constancy Domains

This leaf packages the source notion that a pointwise derived functor is defined at an object:
the localization-indexed diagram is essentially constant.  It provides the triangulated-domain
and two-out-of-three API separately from the weaker existence-only domain, together with the
canonical distinguished triangle on derived values.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits MorphismProperty ObjectProperty Pretriangulated
open scoped ZeroObject

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  {F : D ⥤ D'} {S : MorphismProperty D}

section Stability

variable [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

/-- The right-derived indexing diagram at a zero object is essentially constant. -/
@[stacks 05SC "right-derived source-definedness at zero"]
theorem Functor.RightDerived.DefinedAt.zero : Functor.RightDerived.DefinedAt F S (0 : D) := sorry

/-- The left-derived indexing diagram at a zero object is essentially constant. -/
@[stacks 05SC "left-derived source-definedness at zero"]
theorem Functor.LeftDerived.DefinedAt.zero : Functor.LeftDerived.DefinedAt F S (0 : D) := sorry

end Stability

/-- The objects where the right-derived indexing diagram is essentially constant form a
triangulated object property. -/
@[stacks 05SC "triangulated essential-constancy domain for right-derived values"]
instance Functor.RightDerived.DefinedAt.triangulated
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.RightDerived.DefinedAt.objects F S).IsTriangulated := sorry

/-- The objects where the left-derived indexing diagram is essentially constant form a
triangulated object property. -/
@[stacks 05SC "triangulated essential-constancy domain for left-derived values"]
instance Functor.LeftDerived.DefinedAt.triangulated
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.LeftDerived.DefinedAt.objects F S).IsTriangulated := sorry

/-- The right-derived functor on the essential-constancy domain is triangulated. -/
@[stacks 05SE "right-derived functor on the essential-constancy domain"]
instance Functor.RightDerived.DefinedAt.functor.isTriangulated
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.RightDerived.DefinedAt.functor F S).IsTriangulated := sorry

/-- The left-derived functor on the essential-constancy domain is triangulated. -/
@[stacks 05SE "left-derived functor on the essential-constancy domain"]
instance Functor.LeftDerived.DefinedAt.functor.isTriangulated
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.LeftDerived.DefinedAt.functor F S).IsTriangulated := sorry

/-- The localization factorization of the right-derived functor on the essential-constancy
domain is triangulated. -/
@[stacks 05SE "triangulated right-derived localization factorization"]
instance Functor.RightDerived.DefinedAt.localizationFactorization.isTriangulated
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.RightDerived.DefinedAt.localizationFactorization F S).IsTriangulated := sorry

/-- The localization factorization of the left-derived functor on the essential-constancy
domain is triangulated. -/
@[stacks 05SE "triangulated left-derived localization factorization"]
instance Functor.LeftDerived.DefinedAt.localizationFactorization.isTriangulated
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation] :
    (Functor.LeftDerived.DefinedAt.localizationFactorization F S).IsTriangulated := sorry

section TwoOutOfThree

variable [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

/-- Right-derived source-definedness at the first two vertices of a
distinguished triangle implies source-definedness at the third vertex. -/
@[stacks 05SC "right-derived two-out-of-three, third vertex"]
theorem Functor.RightDerived.DefinedAt.Triangle.obj₃
    {T : Triangle D} (hT : T ∈ distTriang D)
    [Functor.RightDerived.DefinedAt F S T.obj₁]
    [Functor.RightDerived.DefinedAt F S T.obj₂] :
    Functor.RightDerived.DefinedAt F S T.obj₃ := sorry

/-- Right-derived source-definedness at the last two vertices of a
distinguished triangle implies source-definedness at the first vertex. -/
@[stacks 05SC "right-derived two-out-of-three, first vertex"]
theorem Functor.RightDerived.DefinedAt.Triangle.obj₁
    {T : Triangle D} (hT : T ∈ distTriang D)
    [Functor.RightDerived.DefinedAt F S T.obj₂]
    [Functor.RightDerived.DefinedAt F S T.obj₃] :
    Functor.RightDerived.DefinedAt F S T.obj₁ := sorry

/-- Right-derived source-definedness at the first and third vertices of a
distinguished triangle implies source-definedness at the second vertex. -/
@[stacks 05SC "right-derived two-out-of-three, second vertex"]
theorem Functor.RightDerived.DefinedAt.Triangle.obj₂
    {T : Triangle D} (hT : T ∈ distTriang D)
    [Functor.RightDerived.DefinedAt F S T.obj₁]
    [Functor.RightDerived.DefinedAt F S T.obj₃] :
    Functor.RightDerived.DefinedAt F S T.obj₂ := sorry

/-- Left-derived source-definedness at the first two vertices of a
distinguished triangle implies source-definedness at the third vertex. -/
@[stacks 05SC "left-derived two-out-of-three, third vertex"]
theorem Functor.LeftDerived.DefinedAt.Triangle.obj₃
    {T : Triangle D} (hT : T ∈ distTriang D)
    [Functor.LeftDerived.DefinedAt F S T.obj₁]
    [Functor.LeftDerived.DefinedAt F S T.obj₂] :
    Functor.LeftDerived.DefinedAt F S T.obj₃ := sorry

/-- Left-derived source-definedness at the last two vertices of a
distinguished triangle implies source-definedness at the first vertex. -/
@[stacks 05SC "left-derived two-out-of-three, first vertex"]
theorem Functor.LeftDerived.DefinedAt.Triangle.obj₁
    {T : Triangle D} (hT : T ∈ distTriang D)
    [Functor.LeftDerived.DefinedAt F S T.obj₂]
    [Functor.LeftDerived.DefinedAt F S T.obj₃] :
    Functor.LeftDerived.DefinedAt F S T.obj₁ := sorry

/-- Left-derived source-definedness at the first and third vertices of a
distinguished triangle implies source-definedness at the second vertex. -/
@[stacks 05SC "left-derived two-out-of-three, second vertex"]
theorem Functor.LeftDerived.DefinedAt.Triangle.obj₂
    {T : Triangle D} (hT : T ∈ distTriang D)
    [Functor.LeftDerived.DefinedAt F S T.obj₁]
    [Functor.LeftDerived.DefinedAt F S T.obj₃] :
    Functor.LeftDerived.DefinedAt F S T.obj₂ := sorry

end TwoOutOfThree

section ValueTriangle

/-- If the right-derived functor is source-defined at all three vertices of a
distinguished triangle, its canonical triangle of pointwise values is distinguished. -/
@[stacks 05SC "distinguished triangle of source-defined right-derived values"]
theorem Functor.RightDerived.DefinedAt.Triangle.valueDistinguished
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    [Functor.RightDerived.DefinedAt F S T.obj₁]
    [Functor.RightDerived.DefinedAt F S T.obj₂]
    [Functor.RightDerived.DefinedAt F S T.obj₃] :
    Functor.RightDerived.Value.triangle F S T ∈ distTriang D' := sorry

/-- If the left-derived functor is source-defined at all three vertices of a
distinguished triangle, its canonical triangle of pointwise values is distinguished. -/
@[stacks 05SC "distinguished triangle of source-defined left-derived values"]
theorem Functor.LeftDerived.DefinedAt.Triangle.valueDistinguished
    [CategoryTheory.IsTriangulated D] [CategoryTheory.IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    [Functor.LeftDerived.DefinedAt F S T.obj₁]
    [Functor.LeftDerived.DefinedAt F S T.obj₂]
    [Functor.LeftDerived.DefinedAt F S T.obj₃] :
    Functor.LeftDerived.Value.triangle F S T ∈ distTriang D' := sorry

end ValueTriangle


end CategoryTheory
