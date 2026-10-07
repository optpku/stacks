module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

/-!
# Flatness across thickenings of algebraic spaces

This file records flatness consequences for cartesian commutative diagrams of
thickenings of algebraic spaces.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsThickening

/-- In a cartesian commutative diagram of thickenings of algebraic spaces,
flatness of the closed-fiber morphism lifts to the ambient morphism under the
stated finiteness hypotheses. -/
@[stacks 0CGW]
theorem flatAmbient
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsThickening iB]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    Flat f' := sorry

/-- In a cartesian commutative diagram of thickenings of algebraic spaces, the
target structure morphism is flat at every point in the image of the ambient
morphism. -/
@[stacks 0CGW]
theorem flatAtTarget
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsThickening iB]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    ∀ y' : Points Y', y' ∈ Set.range (Points.map f') → FlatAt pY' y' := sorry

end AlgebraicGeometry.AlgebraicSpace.IsThickening
