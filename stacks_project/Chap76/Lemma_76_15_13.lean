/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.ConormalSequence
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h]
variable (w : i ≫ h' = h)

/- Lemma 76.15.13: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over `B`.
There is a canonical exact sequence `C_{Z/X} ⟶ h^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0`.
The first arrow is induced by `d_{Z'/B}` where `Z'` is the universal first-order
neighbourhood of `Z` over `X`. -/
@[stacks 060F]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.exact_and_epi
      i h' h f w :
    (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.complex i h' h f w).Exact ∧
      Epi (Hom.Differentials.comparison h (𝟙 B) f (h ≫ f)
        (Eq.symm (Category.comp_id (h ≫ f)))))

/- The first arrow `C_{Z/X} ⟶ h^* Ω_{X/B}` is induced by `d_{Z'/B}` of the
universal first-order neighbourhood `Z'` of `Z` over `X`. Here `C_{Z/X}` is
the coborder pullback of `I / I²` along `i`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.conormalMap i h' h f w :
    Hom.conormalSheaf i ⟶ (Modules.pullback h).obj (relativeDifferentials f))

/- The second arrow is the Lemma 76.7.6 comparison
`h^* Ω_{X/B} ⟶ Ω_{Z/B}`. -/
#check
  (Hom.Differentials.comparison h (𝟙 B) f (h ≫ f)
      (Eq.symm (Category.comp_id (h ≫ f))) :
    (Modules.pullback h).obj (relativeDifferentials f) ⟶
      relativeDifferentials (h ≫ f))
