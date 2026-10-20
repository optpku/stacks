/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Invariant.FixedPoints.TensorProduct.Inertia

open scoped TensorProduct Algebra.TensorProduct.Right Algebra.TensorProduct.RightAction

universe u v w

/- Lemma 58.12.3: If a prime `q'` of `A ⊗[FixedPoints.subring R G] R` lies over a prime `q` of `R`,
then the inertia subgroups of `q` and `q'` for the original and right-factor actions agree. -/
@[stacks 0BSS] #check (FixedPoints.Tensor.inertia_eq_of_liesOver :
  ∀ {R : Type u} {G : Type v} {A : Type w}
    [CommRing R] [Group G] [MulSemiringAction G R] [CommRing A]
    [Algebra (FixedPoints.subring R G) A] [Finite G],
    ∀ (q : Ideal R) [q.IsPrime],
      ∀ (q' : Ideal (A ⊗[FixedPoints.subring R G] R)) [q'.IsPrime]
        [q'.LiesOver q],
        q.inertia G = q'.inertia G)
