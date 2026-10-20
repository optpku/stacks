/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification.Dimension
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 37.73.6: if a nonempty Noetherian scheme has finite topological Krull
dimension `d`, then its affine stratification number is at most `d`. -/
@[stacks 0F2X] #check
  (AlgebraicGeometry.Scheme.FiniteAffineStratification.number_le_of_topologicalKrullDim_eq :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [Nonempty X] [AlgebraicGeometry.IsNoetherian X]
      (d : ℕ), topologicalKrullDim X = (d : WithBot ℕ∞) →
        AlgebraicGeometry.Scheme.FiniteAffineStratification.number X ≤ d)
