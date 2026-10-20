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

/-- The canonical map from the polynomial ring over `ZMod p` to its perfect
closure is flat. -/
@[stacks 0G65]
theorem of_polynomial_flat (p : ℕ) [Fact p.Prime] :
    (of (Polynomial (ZMod p)) p).Flat := sorry

/-- The canonical map from the polynomial ring over `ZMod p` to its perfect
closure is formally unramified. -/
@[stacks 0G65]
theorem of_polynomial_formallyUnramified (p : ℕ) [Fact p.Prime] :
    (of (Polynomial (ZMod p)) p).FormallyUnramified := sorry

/-- The canonical map from the polynomial ring over `ZMod p` to its perfect
closure is not formally étale. -/
@[stacks 0G65]
theorem of_polynomial_not_formallyEtale (p : ℕ) [Fact p.Prime] :
    ¬ (of (Polynomial (ZMod p)) p).FormallyEtale := sorry

end PerfectClosure
