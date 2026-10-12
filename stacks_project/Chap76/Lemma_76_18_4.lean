/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_18_4_Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsThickening

/- Lemma 76.18.4 (1): under the stated finiteness and cartesian hypotheses for
a commutative diagram of thickenings of algebraic spaces, `f'` is flat. -/
@[stacks 0CGW]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsThickening.flatAmbient :
    {S : Scheme.{u}} →
    {X X' Y Y' B B' : AlgebraicSpace S} →
    {iX : X ⟶ X'} → {iY : Y ⟶ Y'} → {iB : B ⟶ B'} →
    {f : X ⟶ Y} → {f' : X' ⟶ Y'} →
    {pX : X ⟶ B} → {pX' : X' ⟶ B'} → {pY : Y ⟶ B} → {pY' : Y' ⟶ B'} →
    [AlgebraicGeometry.AlgebraicSpace.IsThickening iX] →
    [AlgebraicGeometry.AlgebraicSpace.IsThickening iY] →
    [AlgebraicGeometry.AlgebraicSpace.IsThickening iB] →
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pY'] →
    [AlgebraicGeometry.AlgebraicSpace.Flat pX'] →
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation pX'] →
    [AlgebraicGeometry.AlgebraicSpace.Flat f] →
    CommSq f iX iY f' →
    f ≫ pY = pX → f' ≫ pY' = pX' →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    AlgebraicGeometry.AlgebraicSpace.Flat f')

/- Lemma 76.18.4 (2): under the stated finiteness and cartesian hypotheses for
a commutative diagram of thickenings of algebraic spaces, `pY'` is flat at
every point of `|Y'|` in the image of `|f'|`. -/
@[stacks 0CGW]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsThickening.flatAtTarget :
    {S : Scheme.{u}} →
    {X X' Y Y' B B' : AlgebraicSpace S} →
    {iX : X ⟶ X'} → {iY : Y ⟶ Y'} → {iB : B ⟶ B'} →
    {f : X ⟶ Y} → {f' : X' ⟶ Y'} →
    {pX : X ⟶ B} → {pX' : X' ⟶ B'} → {pY : Y ⟶ B} → {pY' : Y' ⟶ B'} →
    [AlgebraicGeometry.AlgebraicSpace.IsThickening iX] →
    [AlgebraicGeometry.AlgebraicSpace.IsThickening iY] →
    [AlgebraicGeometry.AlgebraicSpace.IsThickening iB] →
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType pY'] →
    [AlgebraicGeometry.AlgebraicSpace.Flat pX'] →
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation pX'] →
    [AlgebraicGeometry.AlgebraicSpace.Flat f] →
    CommSq f iX iY f' →
    f ≫ pY = pX → f' ≫ pY' = pX' →
    IsPullback pX iX iB pX' → IsPullback pY iY iB pY' →
    ∀ y' : AlgebraicGeometry.AlgebraicSpace.Points Y',
      y' ∈ Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map f') →
        AlgebraicGeometry.AlgebraicSpace.FlatAt pY' y')

end AlgebraicGeometry.AlgebraicSpace.IsThickening
