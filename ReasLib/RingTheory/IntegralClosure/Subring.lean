/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integral closure of a subring

This leaf keeps the canonical `integralClosure` subalgebra as the data owner
and exposes the equality criterion for a concrete subring.  No second
integral-closure object is introduced.
-/

universe u

namespace Subring

variable {S : Type u} [CommRing S]

/-- A subring is integrally closed in its ambient ring exactly when it equals
the canonical integral-closure subring. -/
@[stacks 00GP "subring integral-closure criterion"]
theorem isIntegrallyClosedIn_iff_eq_integralClosure (R : Subring S) :
    IsIntegrallyClosedIn R S ↔ R = (integralClosure R S).toSubring := sorry
/- Proof strategy: use `IsIntegrallyClosedIn.integralClosure_eq_bot_iff` for
the canonical subring algebra and identify the bottom subalgebra with `R`. -/

end Subring
