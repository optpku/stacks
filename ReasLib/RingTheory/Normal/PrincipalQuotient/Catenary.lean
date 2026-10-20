/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Catenary.Basic
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.PrincipalQuotient
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Reduced principal quotients in catenary normal local domains

This leaf owns the catenary form of the reduced principal-section theorem.
The radical ideal is kept explicit because later applications choose the
hypersurface inside a prescribed closed subset.

@stack 0BWZ
-/

universe u

namespace IsNormalRing.ReducedPrincipalQuotient

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable [IsLocalRing R] [IsNormalRing R] [IsCatenaryRing R]

/-- Proposition 15.126.10: a nonzero radical ideal in a catenary Noetherian local normal domain
contains a nonzero element whose principal quotient is reduced. -/
@[stacks 0BWZ "Proposition 15.126.10, reduced principal quotient inside a radical ideal"]
theorem exists_mem_radical
    (J : Ideal R) (hJrad : J.IsRadical) (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ principalIdeal f) := sorry
-- Proof strategy: handle dimension zero by showing the local normal domain is
-- a field and taking `f = 1`.  In positive finite dimension, choose a nonzero
-- seed in `J ∩ maximalIdeal R`, complete it to a perturbation-stable parameter
-- system, and maximize the top-dimensional branch count among deep
-- perturbations still lying in `J`.  The 0BWX bound makes the score finite;
-- catenary height control and a final symbolic-power correction force every
-- height-one valuation order to be one, hence the principal quotient reduced.

end IsNormalRing.ReducedPrincipalQuotient
