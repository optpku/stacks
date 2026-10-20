/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.QuasiRegular

@[expose] public section

/-!
# Faithfully Flat Descent for Quasi-Regular Ideals

@stack 068N

This leaf records descent of the principal-open quasi-regular ideal condition
along faithfully flat ring maps.
-/

universe u v

namespace Ideal.IsQuasiRegularIdeal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Lemma 15.32.4 (3), tag `068N`: quasi-regularity of an extended ideal
descends along a faithfully flat ring map. -/
@[stacks 068N "faithfully flat descent of quasi-regular ideals"]
theorem of_faithfullyFlat {f : A →+* B} {I : Ideal A}
    (hff : f.FaithfullyFlat) (hIB : (I.map f).IsQuasiRegularIdeal) :
    I.IsQuasiRegularIdeal := sorry

end Ideal.IsQuasiRegularIdeal
