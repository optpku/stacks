/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Product
import StacksCheckRecall

/-!
# Relative differentials of a fibre product of algebraic spaces

The maps of Lemma 76.7.6 from the pulled-back relative differentials of the factors of a
fibre product of algebraic spaces assemble to an isomorphism onto the relative differentials
of the fibre product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)

/- Lemma 76.7.13: the two canonical projection comparisons identify the relative
differentials of a fibre product of algebraic spaces with the direct sum of the pulled-back
relative differentials of its factors. -/
@[stacks 05ZD] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeDifferentials.Product.comparison_isIso f g :
    IsIso
      (AlgebraicGeometry.AlgebraicSpace.RelativeDifferentials.Product.comparison f g :
        ((Modules.pullback (pullback.fst f g)).obj (relativeDifferentials f) ⊞
          (Modules.pullback (pullback.snd f g)).obj (relativeDifferentials g)) ⟶
            relativeDifferentials (pullback.snd f g ≫ g)))
