/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap106.Definition_106_3_1_Hom
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap106.Lemma_106_5_1_FlatAt

/-!
# Flatness across thickenings of algebraic stacks

This file records flatness consequences for 2-commutative triangles of
thickenings of algebraic stacks whose vertical squares are 2-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, flatness of the closed-fiber morphism
lifts to the ambient morphism under the stated finiteness hypotheses. -/
@[stacks 0CJB]
theorem flatAmbient {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsThickening iB]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : Hom iX iY f f') (hX : Hom iX iB pX pX') (hY : Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX').IsBilimit)
    (pullbackY : (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY').IsBilimit) :
    Flat f' := sorry

/-- In a 2-commutative triangle of thickenings of algebraic stacks whose
vertical squares are 2-fibre products, the target structure morphism is flat
at every point in the image of the ambient morphism. -/
@[stacks 0CJB]
theorem flatAtTarget {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack B] [AlgebraicStack B']
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsThickening iB]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : Hom iX iY f f') (hX : Hom iX iB pX pX') (hY : Hom iY iB pY pY')
    (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
    (pullbackX : (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX').IsBilimit)
    (pullbackY : (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY').IsBilimit) :
    ∀ y' : Points Y', y' ∈ Set.range (Points.map f') → FlatAt pY' y' := sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
