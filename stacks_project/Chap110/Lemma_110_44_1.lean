/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.PerfectClosure.Polynomial
import StacksCheckRecall

@[expose] public section

/- Lemma 110.44.1: Let `A = F_p[T]` be the polynomial ring in one variable
over `F_p`, and let `A_perf` denote its perfect closure. Then `A -> A_perf`
is flat and formally unramified, but not formally étale. (1) In particular,
`A -> A_perf` is flat. -/
@[stacks 0G65] #check
  (PerfectClosure.of_polynomial_flat : ∀ (p : ℕ), [Fact p.Prime] →
    (PerfectClosure.of (Polynomial (ZMod p)) p).Flat)

/- Lemma 110.44.1 (2): Let `A = F_p[T]` be the polynomial ring in one
variable over `F_p`, and let `A_perf` denote its perfect closure. Then
`A -> A_perf` is formally unramified. -/
@[stacks 0G65] #check
  (PerfectClosure.of_polynomial_formallyUnramified : ∀ (p : ℕ), [Fact p.Prime] →
    (PerfectClosure.of (Polynomial (ZMod p)) p).FormallyUnramified)

/- Lemma 110.44.1 (3): Let `A = F_p[T]` be the polynomial ring in one
variable over `F_p`, and let `A_perf` denote its perfect closure. Then
`A -> A_perf` is not formally étale. -/
@[stacks 0G65] #check
  (PerfectClosure.of_polynomial_not_formallyEtale : ∀ (p : ℕ), [Fact p.Prime] →
    ¬ (PerfectClosure.of (Polynomial (ZMod p)) p).FormallyEtale)
