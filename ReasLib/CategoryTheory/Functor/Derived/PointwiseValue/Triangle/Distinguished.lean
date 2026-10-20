/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Triangulated
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Triangle.Construction

@[expose] public section

/-!
# Distinguished Pointwise Derived-Value Triangles

This leaf adds distinguishedness to the explicit triangle data from `Triangle.Construction`
under the standard exact-triangulated localization hypotheses.
-/

open CategoryTheory.Limits CategoryTheory.MorphismProperty CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [_root_.CategoryTheory.IsTriangulated D]
  [_root_.CategoryTheory.IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

/-- A distinguished triangle is sent to a distinguished triangle of pointwise right-derived
values whenever all three values are defined. -/
@[stacks 05SC "distinguished triangle of pointwise right-derived values"]
theorem Functor.RightDerived.Value.triangle_distinguished
    (T : Triangle D) (hT : T ∈ distTriang D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    Functor.RightDerived.Value.triangle F S T ∈ distTriang D' := sorry

/-- A distinguished triangle is sent to a distinguished triangle of pointwise left-derived
values whenever all three values are defined. -/
@[stacks 05SC "distinguished triangle of pointwise left-derived values"]
theorem Functor.LeftDerived.Value.triangle_distinguished
    (T : Triangle D) (hT : T ∈ distTriang D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    Functor.LeftDerived.Value.triangle F S T ∈ distTriang D' := sorry


end CategoryTheory
