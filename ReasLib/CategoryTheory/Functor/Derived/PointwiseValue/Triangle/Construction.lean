/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift
public import Mathlib.CategoryTheory.Triangulated.Basic

@[expose] public section

/-!
# Triangles of Pointwise Derived Values

This leaf packages the three pointwise derived values of a triangle into explicit right- and
left-derived triangles.  It assumes only pointwise existence and shift compatibility; no
pretriangulated or distinguishedness hypotheses enter the data layer.
-/

open CategoryTheory.MorphismProperty CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]

/-- The canonical triangle on the pointwise right-derived values of the vertices and morphisms of
`T`.  All three pointwise values are explicit prerequisites of this data owner. -/
@[stacks 05SC "triangle of pointwise right-derived values"]
noncomputable abbrev Functor.RightDerived.Value.triangle
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] : Triangle D' :=
  Triangle.mk (CategoryTheory.Functor.RightDerived.Value.map F S T.mor₁) (CategoryTheory.Functor.RightDerived.Value.map F S T.mor₂)
    (CategoryTheory.Functor.RightDerived.Value.map F S T.mor₃ ≫
      (Functor.RightDerived.Value.Shift.valueIso F S T.obj₁ (1 : ℤ)).hom)

/-- The first object of `Functor.RightDerived.Value.triangle` is the first pointwise right-derived value. -/
@[simp]
theorem Functor.RightDerived.Value.triangle.obj₁
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    (Functor.RightDerived.Value.triangle F S T).obj₁ = CategoryTheory.Functor.RightDerived.Value.obj F S T.obj₁ := sorry

/-- The second object of `Functor.RightDerived.Value.triangle` is the second pointwise right-derived value. -/
@[simp]
theorem Functor.RightDerived.Value.triangle.obj₂
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    (Functor.RightDerived.Value.triangle F S T).obj₂ = CategoryTheory.Functor.RightDerived.Value.obj F S T.obj₂ := sorry

/-- The third object of `Functor.RightDerived.Value.triangle` is the third pointwise right-derived value. -/
@[simp]
theorem Functor.RightDerived.Value.triangle.obj₃
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    (Functor.RightDerived.Value.triangle F S T).obj₃ = CategoryTheory.Functor.RightDerived.Value.obj F S T.obj₃ := sorry

/-- The first morphism of `Functor.RightDerived.Value.triangle` is the map induced by `T.mor₁`. -/
@[simp]
theorem Functor.RightDerived.Value.triangle.mor₁
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    (Functor.RightDerived.Value.triangle F S T).mor₁ = CategoryTheory.Functor.RightDerived.Value.map F S T.mor₁ := sorry

/-- The second morphism of `Functor.RightDerived.Value.triangle` is the map induced by `T.mor₂`. -/
@[simp]
theorem Functor.RightDerived.Value.triangle.mor₂
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    (Functor.RightDerived.Value.triangle F S T).mor₂ = CategoryTheory.Functor.RightDerived.Value.map F S T.mor₂ := sorry

/-- The third morphism of `Functor.RightDerived.Value.triangle` is the pointwise map induced by `T.mor₃`,
followed by the canonical shift comparison. -/
@[simp]
theorem Functor.RightDerived.Value.triangle.mor₃
    (T : Triangle D)
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseRightDerivedFunctorAt S T.obj₃] :
    (Functor.RightDerived.Value.triangle F S T).mor₃ =
      CategoryTheory.Functor.RightDerived.Value.map F S T.mor₃ ≫
        (Functor.RightDerived.Value.Shift.valueIso F S T.obj₁ (1 : ℤ)).hom := sorry

/-- The canonical triangle on the pointwise left-derived values of the vertices and morphisms of
`T`.  All three pointwise values are explicit prerequisites of this data owner. -/
@[stacks 05SC "triangle of pointwise left-derived values"]
noncomputable abbrev Functor.LeftDerived.Value.triangle
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] : Triangle D' :=
  Triangle.mk (CategoryTheory.Functor.LeftDerived.Value.map F S T.mor₁) (CategoryTheory.Functor.LeftDerived.Value.map F S T.mor₂)
    (CategoryTheory.Functor.LeftDerived.Value.map F S T.mor₃ ≫
      (Functor.LeftDerived.Value.Shift.valueIso F S T.obj₁ (1 : ℤ)).hom)

/-- The first object of `Functor.LeftDerived.Value.triangle` is the first pointwise left-derived value. -/
@[simp]
theorem Functor.LeftDerived.Value.triangle.obj₁
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    (Functor.LeftDerived.Value.triangle F S T).obj₁ = CategoryTheory.Functor.LeftDerived.Value.obj F S T.obj₁ := sorry

/-- The second object of `Functor.LeftDerived.Value.triangle` is the second pointwise left-derived value. -/
@[simp]
theorem Functor.LeftDerived.Value.triangle.obj₂
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    (Functor.LeftDerived.Value.triangle F S T).obj₂ = CategoryTheory.Functor.LeftDerived.Value.obj F S T.obj₂ := sorry

/-- The third object of `Functor.LeftDerived.Value.triangle` is the third pointwise left-derived value. -/
@[simp]
theorem Functor.LeftDerived.Value.triangle.obj₃
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    (Functor.LeftDerived.Value.triangle F S T).obj₃ = CategoryTheory.Functor.LeftDerived.Value.obj F S T.obj₃ := sorry

/-- The first morphism of `Functor.LeftDerived.Value.triangle` is the map induced by `T.mor₁`. -/
@[simp]
theorem Functor.LeftDerived.Value.triangle.mor₁
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    (Functor.LeftDerived.Value.triangle F S T).mor₁ = CategoryTheory.Functor.LeftDerived.Value.map F S T.mor₁ := sorry

/-- The second morphism of `Functor.LeftDerived.Value.triangle` is the map induced by `T.mor₂`. -/
@[simp]
theorem Functor.LeftDerived.Value.triangle.mor₂
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    (Functor.LeftDerived.Value.triangle F S T).mor₂ = CategoryTheory.Functor.LeftDerived.Value.map F S T.mor₂ := sorry

/-- The third morphism of `Functor.LeftDerived.Value.triangle` is the pointwise map induced by `T.mor₃`,
followed by the canonical shift comparison. -/
@[simp]
theorem Functor.LeftDerived.Value.triangle.mor₃
    (T : Triangle D)
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₁]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₂]
    [F.HasPointwiseLeftDerivedFunctorAt S T.obj₃] :
    (Functor.LeftDerived.Value.triangle F S T).mor₃ =
      CategoryTheory.Functor.LeftDerived.Value.map F S T.mor₃ ≫
        (Functor.LeftDerived.Value.Shift.valueIso F S T.obj₁ (1 : ℤ)).hom := sorry



end CategoryTheory
