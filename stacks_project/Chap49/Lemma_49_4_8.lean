/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Module.RelativeDualizing.TraceElement.LocalAlgebra
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 49.4.8: for a finite-dimensional local `k`-algebra `A`, nonvanishing of
the algebra trace, the canonical relative-dualizing trace element, and the
residue-field length criterion are equivalent. -/
@[stacks 0C13] #check
  (Algebra.trace_ne_zero_tfae_of_isLocalRing :
    ∀ (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
      [FiniteDimensional k A] [IsLocalRing A],
      List.TFAE [Algebra.trace k A ≠ 0,
        @Algebra.RelativeDualizingModule.finiteFlatTraceElement k A _ _ _
          (IsNoetherianRing.of_finite k A) _ _ _ ≠ 0,
        Algebra.IsSeparable k (IsLocalRing.ResidueField A) ∧
          DVR.Field.PrimeToChar k (Module.length A A).toNat])
