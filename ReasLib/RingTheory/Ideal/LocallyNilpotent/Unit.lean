/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Units modulo locally nilpotent ideals

This leaf owns the element-level quotient criterion.  The ideal and its
local-nilpotence proof remain explicit because they describe the particular
quotient map under consideration.
-/

universe u

namespace Ideal.IsLocallyNilpotent

variable {R : Type u} [CommRing R]

/-- Lemma 10.32.4: units are detected after quotienting by a locally nilpotent ideal. -/
@[stacks 0AMG "unit criterion for a locally nilpotent quotient"]
theorem isUnit_iff_quotient_mk
    (I : Ideal R) (hI : I.IsLocallyNilpotent) {x : R} :
    IsUnit x ↔ IsUnit (Ideal.Quotient.mk I x) := sorry

end Ideal.IsLocallyNilpotent
