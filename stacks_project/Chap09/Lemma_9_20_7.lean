/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Trace.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Lemma 9.20.7:
- primary domain: separability criteria for finite field extensions via the trace map and trace
  pairing;
- sampled owner declarations:
  `Algebra.trace`,
  `Algebra.traceForm`,
  `Algebra.traceForm_nondegenerate`,
  `traceForm_nondegenerate_tfae`;
- best owner abstraction:
  - `source-facing`: the equivalence between separability of `L/K`, nonvanishing of the trace, and
    nondegeneracy of the trace pairing;
  - `core/canonical`: the mathlib theorem `traceForm_nondegenerate_tfae`;
  - `bridge/view`: the forward implications `Algebra.traceForm_nondegenerate` and
    `Algebra.trace_ne_zero`, derived from the same owner theorem;
- primitive data: the finite extension `L/K` together with the canonical owners
  `Algebra.trace K L` and `Algebra.traceForm K L`;
- derived API: the TFAE packaging of the three equivalent criteria.

This item is therefore already at the correct `core/canonical` layer, so refinement should remain
direct check of `traceForm_nondegenerate_tfae` rather than introducing a parallel local
separability criterion.
-/

/- Lemma 9.20.7: for a finite field extension `L/K`, the following are equivalent: the extension
`L/K` is separable, the trace map `Algebra.trace K L` is not identically zero, and the trace
pairing `Algebra.traceForm K L` is nondegenerate. This is the canonical theorem
`traceForm_nondegenerate_tfae`. -/
@[stacks 0BIL]
#check traceForm_nondegenerate_tfae
