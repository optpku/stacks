/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Henselization.Quotient
public import ReasLib.RingTheory.Henselian.Henselization.Reduced
public import ReasLib.RingTheory.Henselian.StrictHenselization.Quotient
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nilradicals and henselization

The nilradical of a local ring extends to the nilradical of either kind of
henselization.

@stack 0ASE
-/

@[expose] public section

universe u v

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- Lemma 15.45.5 (1) (0ASE): the extension of the nilradical to a
henselization is its nilradical. -/
@[stacks 0ASE "Lemma 15.45.5 (1): nilradical of a henselization"]
theorem map_nilradical :
    Ideal.map (algebraMap R S) (nilradical R) = nilradical S := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- Lemma 15.45.5 (2) (0ASE): the extension of the nilradical to a
strict henselization is its nilradical. -/
@[stacks 0ASE "Lemma 15.45.5 (2): nilradical of a strict henselization"]
theorem map_nilradical :
    Ideal.map (algebraMap R S) (nilradical R) = nilradical S := sorry

end IsStrictHenselizationOf
