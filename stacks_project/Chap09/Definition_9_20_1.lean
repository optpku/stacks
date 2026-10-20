/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Norm.Defs
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Definition 9.20.1:
- primary domain: trace and norm for finite field extensions;
- sampled owner declarations: `Algebra.trace`, `Algebra.trace_apply`, `Algebra.norm`,
  `Algebra.norm_apply`;
- `source-facing`: the textbook trace and norm of a finite extension `L/K`;
- `core/canonical`: the mathlib owners `Algebra.trace K L` and `Algebra.norm K`;
- `bridge/view`: the companion formulas expressing them as the trace and determinant of
  left-multiplication by an element.

Primitive data are only the canonical owner maps `Algebra.trace K L` and `Algebra.norm K`; the
left-multiplication formulas are derived API, so this file should stay at direct check/use rather
than introducing parallel local definitions.
-/

/- Definition 9.20.1 (1): for a finite field extension `L/K`, the trace `Trace_{L/K}` is the
canonical linear map `Algebra.trace K L`, sending `α : L` to the trace over `K` of multiplication
by `α` on `L`. -/
@[stacks 0BIF]
#check Algebra.trace

/- Companion check: the defining formula for the trace is the existing theorem
`Algebra.trace_apply`, identifying `Algebra.trace K L α` with the trace of the left-multiplication
linear endomorphism by `α`. -/
#check Algebra.trace_apply

/- Definition 9.20.1 (2): for a finite field extension `L/K`, the norm `Norm_{L/K}` is the
canonical multiplicative map `Algebra.norm K`, sending `α : L` to the determinant over `K` of
multiplication by `α` on `L`. -/
#check Algebra.norm

/- Companion check: the defining formula for the norm is the existing theorem
`Algebra.norm_apply`, identifying `Algebra.norm K α` with the determinant of the
left-multiplication linear endomorphism by `α`. -/
#check Algebra.norm_apply
