/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FlatAt

/-!
# Flatness across thickenings of algebraic stacks

Flatness lifts across cartesian diagrams of thickenings when the ambient source
is flat and locally of finite presentation over the base and the ambient target
is locally of finite type over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

/-- In a 2-commutative triangle of thickenings of algebraic stacks with
cartesian vertical squares, suppose the ambient target is locally of finite
type over the base, the ambient source is flat and locally of finite
presentation over the base, and the closed-fiber morphism is flat. Then the
ambient morphism is flat, and the ambient target is flat over the base at
every point in the image of the ambient morphism. -/
@[stacks 0CJB]
theorem flatAmbient_and_flatAtTarget
    {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsThickening iB]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : Hom iX iY f f') (hX : Hom iX iB pX pX') (hY : Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : PseudoPullbackCone.IsBilimit
      (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
    (pullbackY : PseudoPullbackCone.IsBilimit
      (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')) :
    Flat f' ∧
      (∀ y' : Points Y', y' ∈ Set.range (Points.map f') →
        existsFlatAtPointSquare pY' y') := sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
