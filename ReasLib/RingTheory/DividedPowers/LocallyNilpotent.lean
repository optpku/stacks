/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.LocallyNilpotent

@[expose] public section

/-!
# Locally Nilpotent Divided-Power Ideals

This module connects a divided power structure to local nilpotence of its ideal.
-/

universe u

namespace Ideal

variable {p : ℕ} {A : Type u} [CommRing A]

/-- Lemma 23.2.6 (Tag 07GR), forward bridge: nilpotence of p modulo a locally nilpotent ideal
forces nilpotence of p in the ambient ring. -/
theorem IsLocallyNilpotent.isNilpotent_natCast_of_quotient {I : Ideal A}
    (hI : I.IsLocallyNilpotent) (hp : IsNilpotent (p : A ⧸ I)) :
    IsNilpotent (p : A) := sorry

end Ideal

namespace DividedPowers

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- Lemma 23.2.6 (Tag 07GR), reverse bridge: a divided power structure and nilpotence of p
force its ideal to be locally nilpotent. -/
theorem isLocallyNilpotent_of_isNilpotent_natCast {I : Ideal A} (γ : DividedPowers I)
    (hpA : IsNilpotent (p : A)) :
    I.IsLocallyNilpotent := sorry

/-- Lemma 23.2.6 (Tag 07GR): under quotient nilpotence of p, a divided-power ideal is locally
nilpotent exactly when p is nilpotent in the ambient ring. -/
@[stacks 07GR]
theorem isLocallyNilpotent_iff_isNilpotent_natCast {I : Ideal A} (γ : DividedPowers I)
    (hp : IsNilpotent (p : A ⧸ I)) :
    I.IsLocallyNilpotent ↔ IsNilpotent (p : A) := sorry

end DividedPowers
