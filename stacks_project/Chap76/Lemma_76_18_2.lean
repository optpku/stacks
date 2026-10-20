/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Thickening.Flat
import StacksCheckRecall

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

/- Lemma 76.18.2 (1): in a commutative diagram of thickenings of algebraic spaces
over a scheme `S` with cartesian vertical squares, if the base thickening `B ⟶ B'`
has finite order, `X'` is flat over `B'`, and `f` is flat, then `f'` is flat. -/
@[stacks 0CG5]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.flatAmbient :
    {S : Scheme.{u}} → {X X' Y Y' B B' : AlgebraicSpace S} →
    {iX : X ⟶ X'} → {iY : Y ⟶ Y'} → {iB : B ⟶ B'} →
    {f : X ⟶ Y} → {f' : X' ⟶ Y'} →
    {pX : X ⟶ B} → {pX' : X' ⟶ B'} → {pY : Y ⟶ B} → {pY' : Y' ⟶ B'} →
    [IsThickening iX] → [IsThickening iY] → [IsFiniteOrderThickening iB] →
    [Flat pX'] → [Flat f] →
    CommSq f iX iY f' →
    f ≫ pY = pX → f' ≫ pY' = pX' →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    Flat f')

/- Lemma 76.18.2 (2): in a commutative diagram of thickenings of algebraic spaces
over a scheme `S` with cartesian vertical squares, if the base thickening `B ⟶ B'`
has finite order, `X'` is flat over `B'`, and `f` is flat, then `Y'` is flat over
`B'` at every point in the image of `f'`. -/
@[stacks 0CG5]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.flatAtTarget :
    {S : Scheme.{u}} → {X X' Y Y' B B' : AlgebraicSpace S} →
    {iX : X ⟶ X'} → {iY : Y ⟶ Y'} → {iB : B ⟶ B'} →
    {f : X ⟶ Y} → {f' : X' ⟶ Y'} →
    {pX : X ⟶ B} → {pX' : X' ⟶ B'} → {pY : Y ⟶ B} → {pY' : Y' ⟶ B'} →
    [IsThickening iX] → [IsThickening iY] → [IsFiniteOrderThickening iB] →
    [Flat pX'] → [Flat f] →
    CommSq f iX iY f' →
    f ≫ pY = pX → f' ≫ pY' = pX' →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    ∀ y' : Points Y', y' ∈ Set.range (Points.map f') → FlatAt pY' y')

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
