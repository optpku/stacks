/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Maximal

/-!
# Maximal Cohen--Macaulay modules over regular local rings

This leaf owns the reusable freeness criterion.  The hypotheses are stated
using the canonical `Module.MaximalCohenMacaulay` predicate; no resolution,
parameter system, or chosen basis is part of the public interface.

@stack 00NT
-/

@[expose] public section

universe u v

namespace Module.MaximalCohenMacaulay

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The depth of a maximal Cohen--Macaulay module over a regular local ring is the span rank of
the maximal ideal. -/
@[stacks 00NT "depth of a maximal Cohen--Macaulay module"]
theorem moduleDepth_eq_spanFinrank_maximalIdeal
    (hMCM : Module.MaximalCohenMacaulay R M) :
    moduleDepth R M = (IsLocalRing.maximalIdeal R).spanFinrank := sorry

/-- Tag `00NT`: a maximal Cohen--Macaulay module over a regular local ring is free. -/
@[stacks 00NT "maximal Cohen--Macaulay modules over regular local rings are free"]
theorem free_of_isRegularLocalRing
    (hMCM : Module.MaximalCohenMacaulay R M) :
    Module.Free R M := sorry

end Module.MaximalCohenMacaulay
