/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Quotient
public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.LocalRing.ResidueField.Quotient

@[expose] public section

/-!
# Quotients of Strictly Henselian Local Rings

@stack 05WS

This leaf owns strict henselianity for proper quotients.  It depends on the
ordinary henselian quotient API and the residue-field quotient equivalence used
to transport separable closedness, without making the ordinary henselian layer
depend on strict henselian local rings.
-/

universe u

namespace StrictHenselianLocalRing

/-- Tag `05WS`: a proper quotient of a strictly henselian local ring is strictly henselian. -/
@[stacks 05WS "strict henselian proper quotient"]
theorem quotient {R : Type u} [CommRing R] [StrictHenselianLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) : StrictHenselianLocalRing (R ⧸ I) := sorry

end StrictHenselianLocalRing
