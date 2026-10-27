/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.Differentials.ConormalTransitivity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.19.14: Let `S` be a scheme and let `Z ⟶ X ⟶ Y` be a commutative
triangle of algebraic spaces over `S`. If `i : Z ⟶ X` and `j : Z ⟶ Y` are
formally unramified and `f : X ⟶ Y` is formally smooth, the canonical sequence
`0 ⟶ C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0` is exact and étale-locally split.
Here `i = iX ≫ fX` and `j = iY ≫ fY` are presented by arbitrary universal
first-order thickenings. The first two terms are `Hom.conormalSheaf iY` and
`Hom.conormalSheaf iX`, and the last term is
`(Modules.pullback (iX ≫ fX)).obj (Hom.relativeDifferentials f)`.
The first arrow is `IsUniversalFirstOrder.Differentials.Transitivity.projection`,
the conormal comparison composed with the inverse identity-pullback comparison.
The second arrow is
`IsUniversalFirstOrder.Differentials.conormalMap iX fX (iX ≫ fX) f rfl`.
Local splitting is along a covering family indexed by `I : Type u` in the
small étale site of `Z`, after pullback along each chart's structural morphism. -/
@[stacks 06BK] #check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.Transitivity.shortExact_and_etaleLocallySplit :
    ∀ {S : Scheme.{u}} {X Y Z ZX ZY : AlgebraicSpace S}
      (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y) (f : X ⟶ Y)
      [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
      [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
      (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) [FormallySmooth f],
      (IsUniversalFirstOrder.Differentials.Transitivity.complex iX fX iY fY f sq).ShortExact ∧
        IsUniversalFirstOrder.Differentials.Transitivity.IsEtaleLocallySplit iX fX iY fY f sq)
