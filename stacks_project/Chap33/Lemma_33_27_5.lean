/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Normalization.Comparison

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.27.5 (1): For a separable field extension, the canonical morphism from the
normalization after base change to the base change of the normalization is an isomorphism. -/
@[stacks 0C3N] #check
  (AlgebraicGeometry.FieldExtension.Normalization.comparison_isIso_of_isSeparable :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.LocallyAlgebraic X] [Algebra.IsSeparableOver k K],
      CategoryTheory.IsIso
        ((AlgebraicGeometry.FieldExtension.Normalization.comparison X) :
          (AlgebraicGeometry.FieldExtension.baseChange k K X.hom).normalization ⟶
            AlgebraicGeometry.FieldExtension.baseChange k K
              (X.left.normalizationTo ≫ X.hom)))

/- Lemma 33.27.5 (2): For every field extension, the canonical morphism from the
normalization after base change to the base change of the normalization is a universal
homeomorphism. -/
@[stacks 0C3N] #check
  (AlgebraicGeometry.FieldExtension.Normalization.comparison_universalHomeomorphism :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.LocallyAlgebraic X],
      AlgebraicGeometry.UniversalHomeomorphism
        ((AlgebraicGeometry.FieldExtension.Normalization.comparison X) :
          (AlgebraicGeometry.FieldExtension.baseChange k K X.hom).normalization ⟶
            AlgebraicGeometry.FieldExtension.baseChange k K
              (X.left.normalizationTo ≫ X.hom)))
