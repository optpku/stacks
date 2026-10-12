/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder

/-!
# Flatness of morphisms of thickenings of algebraic spaces

In a cartesian commutative diagram of thickenings of algebraic spaces over a
scheme, if the base thickening has finite order, the ambient source is flat over
the thickened base, and the closed-fiber map is flat, then the ambient map is
flat and the target is flat over the thickened base at points in its image.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

/-- Lemma 76.18.2 (1): in a commutative diagram of thickenings of algebraic spaces
over a scheme `S` with cartesian vertical squares, if the base thickening `B ⟶ B'`
has finite order, `X'` is flat over `B'`, and `f` is flat, then `f'` is flat. -/
@[stacks 0CG5]
theorem flatAmbient
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsFiniteOrderThickening iB]
    [Flat pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    Flat f' :=
  sorry

/-- Lemma 76.18.2 (2): in a commutative diagram of thickenings of algebraic spaces
over a scheme `S` with cartesian vertical squares, if the base thickening `B ⟶ B'`
has finite order, `X'` is flat over `B'`, and `f` is flat, then `Y'` is flat over
`B'` at every point in the image of `f'`. -/
@[stacks 0CG5]
theorem flatAtTarget
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsFiniteOrderThickening iB]
    [Flat pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    ∀ y' : Points Y', y' ∈ Set.range (Points.map f') → FlatAt pY' y' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
