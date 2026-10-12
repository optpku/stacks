/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.QuotSMulTop

/-!
# Flatness Across a Regular Element

This leaf owns the principal regular-element criterion that reconstructs flatness,
or faithful flatness, from the localization away from the element and its quotient.

@stack 0H7N
-/

@[expose] public section

universe u v

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.99.16 (1): flatness of `M` follows from flatness away from a regular
element and flatness of the corresponding principal quotient. -/
@[stacks 0H7N "flatness across a regular element"]
theorem of_regular_element (f : R) (hfR : IsRegular f) (hfM : IsSMulRegular M f)
    [Module.Flat (Localization.Away f) (LocalizedModule.Away f M)]
    [Module.Flat (R ⧸ Ideal.span ({f} : Set R)) (QuotSMulTop f M)] :
    Module.Flat R M := sorry

end Module.Flat

namespace Module.FaithfullyFlat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.99.16 (2): faithful flatness of `M` follows from faithful
flatness away from a regular element and of the corresponding principal quotient. -/
@[stacks 0H7N "faithful flatness across a regular element"]
theorem of_regular_element (f : R) (hfR : IsRegular f) (hfM : IsSMulRegular M f)
    [Module.FaithfullyFlat (Localization.Away f) (LocalizedModule.Away f M)]
    [Module.FaithfullyFlat (R ⧸ Ideal.span ({f} : Set R)) (QuotSMulTop f M)] :
    Module.FaithfullyFlat R M := sorry

end Module.FaithfullyFlat
