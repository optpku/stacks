/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Dimension
import StacksCheckRecall

universe u v

/- Lemma 29.30.13: a relative global complete-intersection presentation with
`n` generators and `c` relations has fiber-local dimension `n - c` at every
point of its affine spectrum. -/
@[stacks 02K0] #check
  (Algebra.Presentation.IsRelativeGlobalCompleteIntersection.relativeDimensionAt_eq_natSub :
    ∀ {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
      {n c : ℕ} {P : Algebra.Presentation R A (Fin n) (Fin c)},
      P.IsRelativeGlobalCompleteIntersection →
        ∀ q : PrimeSpectrum A,
          relativeDimensionAt R A q = (n - c : WithBot ℕ∞))
