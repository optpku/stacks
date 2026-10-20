/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.Intersection
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.34.3 (1): the intersection is nonempty. -/
@[stacks 0B2R]
#check
  (AlgebraicGeometry.ProjectiveSpace.closedSubset_inter_nonempty_of_dim_add_ge :
    ∀ {k : Type u} [Field k] {n r s : ℕ}
      (X Y : TopologicalSpace.Closeds (AlgebraicGeometry.ProjectiveSpace.scheme k n)),
      (X : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)).Nonempty →
      (Y : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)).Nonempty →
      topologicalKrullDim
          (X : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)) = r →
      topologicalKrullDim
          (Y : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)) = s →
      r + s ≥ n →
      ((X ⊓ Y : TopologicalSpace.Closeds
          (AlgebraicGeometry.ProjectiveSpace.scheme k n)) :
        Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)).Nonempty)

/- Lemma 33.34.3 (2): the intersection has dimension at least `r + s - n`. -/
@[stacks 0B2R]
#check
  (AlgebraicGeometry.ProjectiveSpace.closedSubset_inter_dim_ge_add_sub_of_dim_add_ge :
    ∀ {k : Type u} [Field k] {n r s : ℕ}
      (X Y : TopologicalSpace.Closeds (AlgebraicGeometry.ProjectiveSpace.scheme k n)),
      (X : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)).Nonempty →
      (Y : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)).Nonempty →
      topologicalKrullDim
          (X : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)) = r →
      topologicalKrullDim
          (Y : Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)) = s →
      r + s ≥ n →
      topologicalKrullDim
          ((X ⊓ Y : TopologicalSpace.Closeds
              (AlgebraicGeometry.ProjectiveSpace.scheme k n)) :
            Set (AlgebraicGeometry.ProjectiveSpace.scheme k n)) ≥ r + s - n)
