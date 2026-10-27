/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Crystalline.SquaredOrigin
import StacksCheckRecall

/- The witness prime operation includes `de uv` in characteristic two. This correction
preserves its values on `x²`, `xy`, and `y²`, and hence preserves detection of `τ` by `uv`. -/

/- Example 60.22.1 (1): the explicit completed-envelope element is killed by `p`. -/
@[stacks 07LJ] #check (Crystalline.SquaredOrigin.tau_p_mul :
  ∀ {p : ℕ} [Fact p.Prime] (data : Crystalline.SquaredOrigin.EnvelopeData p),
    (p : data.D) * Crystalline.SquaredOrigin.tau data = 0)

/- Example 60.22.1 (2): the explicit element has zero completed relative differential. -/
@[stacks 07LJ] #check (Crystalline.SquaredOrigin.tau_differential :
  ∀ {p : ℕ} [Fact p.Prime] (data : Crystalline.SquaredOrigin.EnvelopeData p),
    crystallineOmegaD_derivation (Crystalline.SquaredOrigin.envelopeBaseMap data)
      data.γbar p (Crystalline.SquaredOrigin.tau data) = 0)

/- Example 60.22.1 (3): the explicit completed-envelope element is nonzero. -/
@[stacks 07LJ] #check (Crystalline.SquaredOrigin.tau_ne_zero :
  ∀ {p : ℕ} [Fact p.Prime] (data : Crystalline.SquaredOrigin.EnvelopeData p),
    Crystalline.SquaredOrigin.tau data ≠ 0)

/- Example 60.22.1 (4): actual crystalline global functions have nonzero `p`-torsion. -/
@[stacks 07LJ] #check (Crystalline.SquaredOrigin.cohomology_has_p_torsion :
  ∀ (p : ℕ) [Fact p.Prime],
    ∃ t : Crystalline.SquaredOrigin.cohomology p, t ≠ 0 ∧ (p : ℤ) • t = 0)

/- Example 60.22.1 (5): geometric Frobenius pullback on crystalline global functions
is not injective. -/
@[stacks 07LJ] #check (Crystalline.SquaredOrigin.frobeniusPullback_not_injective :
  ∀ (p : ℕ) [Fact p.Prime],
    ¬ Function.Injective (Crystalline.SquaredOrigin.frobeniusOnCohomology p))
