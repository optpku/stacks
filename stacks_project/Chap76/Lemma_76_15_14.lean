/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Differentials.Transitivity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.15.14: Let `S` be a scheme. Let a commutative triangle of algebraic
spaces over `S` have formally unramified morphisms `i : Z ⟶ X` and `j : Z ⟶ Y`.
Then the canonical sequence `C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0` is exact.
Here `i := iX ≫ fX` and `j := iY ≫ fY` are presented by arbitrary universal
first-order thickenings, and the two conormal terms are `Hom.conormalSheaf iY`
and `Hom.conormalSheaf iX`. The last term is
`(Modules.pullback (iX ≫ fX)).obj (Hom.relativeDifferentials f)`.
The first arrow, from Lemma 76.15.8, is
`IsUniversalFirstOrder.conormalMap iX fX iY fY (𝟙 Z) f sq`, preceded by
`(SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf iY)`.
The second arrow, from Lemma 76.15.13, is
`IsUniversalFirstOrder.Differentials.conormalMap iX fX (iX ≫ fX) f rfl`.
Exactness at the middle term and epimorphy of the second arrow express the
terminal zero. -/
@[stacks 06BE] #check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.Transitivity.exact_and_epi :
    ∀ {S : Scheme.{u}} {X Y Z ZX ZY : AlgebraicSpace S}
      (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y) (f : X ⟶ Y)
      [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
      [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
      (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f),
      (IsUniversalFirstOrder.Differentials.Transitivity.complex iX fX iY fY f sq).Exact ∧
        Epi (IsUniversalFirstOrder.Differentials.conormalMap iX fX (iX ≫ fX) f rfl))

