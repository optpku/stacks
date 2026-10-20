/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.37.6: A principal ideal domain is normal.

The canonical owner is `GCDMonoid.toIsIntegrallyClosed`; this file records the source-facing
recall without introducing a chapter alias.

@stack 00GZ
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/- Lemma 10.37.6: a principal ideal domain is normal, i.e. it is integrally closed in its
fraction field. The owner abstraction here is the canonical typeclass `IsIntegrallyClosed R`,
while the primitive source data are just the PID hypotheses. A PID canonically carries a
`GCDMonoid` structure, so this is the direct upstream bridge `GCDMonoid.toIsIntegrallyClosed`. -/
@[stacks 00GZ]
#check @GCDMonoid.toIsIntegrallyClosed
