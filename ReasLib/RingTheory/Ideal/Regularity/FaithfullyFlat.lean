/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Regularity

@[expose] public section

/-!
# Faithfully Flat Descent for H1-Regular Ideals

@stack 068N

This leaf records descent of the principal-open `H_1`-regular ideal condition
along faithfully flat ring maps.
-/

universe u v

namespace Ideal.IsH1RegularIdeal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Lemma 15.32.4 (2), tag `068N`: `H_1`-regularity of an extended ideal
descends along a faithfully flat ring map. -/
@[stacks 068N "faithfully flat descent of H1-regular ideals"]
theorem of_faithfullyFlat {f : A →+* B} {I : Ideal A}
    (hff : f.FaithfullyFlat) (hIB : (I.map f).IsH1RegularIdeal) :
    I.IsH1RegularIdeal := sorry

end Ideal.IsH1RegularIdeal
