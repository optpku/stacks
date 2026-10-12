/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.10.2 (1): in a commutative diagram of thickenings with cartesian vertical
squares, if the base thickening has finite order, `X'` is flat over `S'`, and `f` is
flat, then `f'` is flat. -/
@[stacks 06AF] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.flatAmbient :
    ∀ {X X' Y Y' S S' : AlgebraicGeometry.Scheme.{u}}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
    [AlgebraicGeometry.IsThickening iX] [AlgebraicGeometry.IsThickening iY]
    [AlgebraicGeometry.IsFiniteOrderThickening iS]
    [AlgebraicGeometry.Flat pX'] [AlgebraicGeometry.Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iS pX')
    (pullbackY : IsPullback pY iY iS pY'),
    AlgebraicGeometry.Flat f')

/- Lemma 37.10.2 (2): in a commutative diagram of thickenings with cartesian vertical
squares, if the base thickening has finite order, `X'` is flat over `S'`, and `f` is
flat, then `pY'` is flat at every point in the image of `f'`. -/
@[stacks 06AF] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.flatAtTarget :
    ∀ {X X' Y Y' S S' : AlgebraicGeometry.Scheme.{u}}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
    [AlgebraicGeometry.IsThickening iX] [AlgebraicGeometry.IsThickening iY]
    [AlgebraicGeometry.IsFiniteOrderThickening iS]
    [AlgebraicGeometry.Flat pX'] [AlgebraicGeometry.Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iS pX')
    (pullbackY : IsPullback pY iY iS pY'),
    ∀ y' : Y', y' ∈ Set.range f' → pY'.flatAt y')
