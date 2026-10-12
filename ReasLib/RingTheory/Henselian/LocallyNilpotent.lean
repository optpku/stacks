/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Henselian
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Henselian pairs from locally nilpotent ideals

@stack 0ALI
-/

@[expose] public section

universe u

namespace Ideal.IsLocallyNilpotent

/-- A locally nilpotent ideal defines a henselian pair.

This is a method on the explicit local-nilpotence proof, not a global instance: an arbitrary ideal
does not carry canonical evidence of local nilpotence. -/
@[stacks 0ALI "locally nilpotent ideals are henselian"]
theorem henselianRing {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I.IsLocallyNilpotent) : HenselianRing A I := sorry

end Ideal.IsLocallyNilpotent
