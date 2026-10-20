/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Extension
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.2.1: an affine étale morphism over an affine closed subscheme extends to
an affine étale morphism over the ambient affine scheme, with the original morphism
identified with its pullback as a scheme over the closed subscheme. -/
@[stacks 057R] #check
  (AlgebraicGeometry.Etale.exists_affine_extension_of_closedImmersion :
    ∀ {X Z Z' : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Z]
      [AlgebraicGeometry.IsClosedImmersion i]
      (g : Z' ⟶ Z) [AlgebraicGeometry.IsAffine Z'] [AlgebraicGeometry.Etale g],
      ∃ (X' : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsAffine X')
        (f : X' ⟶ X) (_ : AlgebraicGeometry.Etale f),
        Nonempty (CategoryTheory.Over.mk g ≅
          CategoryTheory.Over.mk (CategoryTheory.Limits.pullback.fst i f)))
