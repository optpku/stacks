/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DimensionZero
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.20.2: a locally algebraic scheme over a field of dimension zero is a
disjoint union of spectra of finite-dimensional local Artinian algebras. -/
@[stacks 06LH]
#check
  (AlgebraicGeometry.SchemeOverField.FiniteLocalArtinianCoproduct.exists_of_locallyAlgebraic_of_dimZero :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
        [AlgebraicGeometry.LocallyAlgebraic X],
      topologicalKrullDim X.left = 0 →
        Nonempty
          (AlgebraicGeometry.SchemeOverField.FiniteLocalArtinianCoproduct X))

#check
  (AlgebraicGeometry.Algebraic.isAffine_of_dimZero :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
        [AlgebraicGeometry.Algebraic X],
      topologicalKrullDim X.left = 0 → AlgebraicGeometry.IsAffine X.left)

#check
  (AlgebraicGeometry.Algebraic.isFinite_of_dimZero :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
        [AlgebraicGeometry.Algebraic X],
      topologicalKrullDim X.left = 0 → AlgebraicGeometry.IsFinite X.hom)
