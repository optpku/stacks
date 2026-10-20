/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.PrincipalQuotient
import StacksCheckRecall

@[expose] public section

open IsNormalRing.ReducedPrincipalQuotient

/-!
# Lemma 15.126.5

@stack 0AXH

The finite family of pairwise distinct height-one primes is represented by a
`Finset` of prime-spectrum points in the shared normal-domain API.
-/

/- Lemma 15.126.5: finitely many height-one primes contain a common nonzero element defining a
reduced principal quotient. -/
@[stacks 0AXH "Lemma 15.126.5, reduced principal quotient through height-one primes"]
#check @exists_mem_heightOne
