module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

namespace PerfectClosure

/-- Lemma 110.44.1 (1): the canonical map `PerfectClosure.of` from
`A = Polynomial (ZMod p)` to `A_perf = PerfectClosure A p` is flat. -/
@[stacks 0G65]
theorem of_polynomial_flat (p : ℕ) [Fact p.Prime] :
    (of (Polynomial (ZMod p)) p).Flat := sorry

/-- Lemma 110.44.1 (2): the canonical map `PerfectClosure.of` from
`A = Polynomial (ZMod p)` to `A_perf = PerfectClosure A p` is formally unramified. -/
@[stacks 0G65]
theorem of_polynomial_formallyUnramified (p : ℕ) [Fact p.Prime] :
    (of (Polynomial (ZMod p)) p).FormallyUnramified := sorry

/-- Lemma 110.44.1 (3): the canonical map `PerfectClosure.of` from
`A = Polynomial (ZMod p)` to `A_perf = PerfectClosure A p` is not formally étale. -/
@[stacks 0G65]
theorem of_polynomial_not_formallyEtale (p : ℕ) [Fact p.Prime] :
    ¬ (of (Polynomial (ZMod p)) p).FormallyEtale := sorry

end PerfectClosure
