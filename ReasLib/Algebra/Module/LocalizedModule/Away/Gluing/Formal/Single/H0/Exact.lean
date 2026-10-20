/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single.H0
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact degree-zero sequences for single-principal-open formal gluing

For a Beauville--Laszlo glueing pair, the three canonical degree-zero
sequences attached to a single-principal-open pullback datum are short exact.
Their concrete maps and `ShortComplex` data are owned by
`LocalizedModule.Away.FormalGluing.Single.H0`; this leaf contains only the
exactness bridges.

@stack 0BP3
@stack 0BP4
@stack 0BP5
-/

@[expose] public section

open LocalizedModule.Away.FormalGluing

universe u

noncomputable section

namespace LocalizedModule.Away.FormalGluing.Single

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 15.91.16.1: for a Beauville--Laszlo glueing pair, the canonical
degree-zero kernel sequence is short exact. -/
@[stacks 0BP3 "single-principal-open H0 short exact sequence"]
theorem h0Sequence_shortExact_of_glueingPair
    (φ : R →+* S) (f : R) (X : Pullback φ f)
    (hpair : IsBeauvilleLaszloGlueingPairAlong φ f) :
    (h0Sequence φ f X).ShortExact := sorry

/-- 15.91.16.2: for a Beauville--Laszlo glueing pair, the canonical sequence
modulo principal-power torsion is short exact. -/
@[stacks 0BP4 "single-principal-open mod-torsion short exact sequence"]
theorem h0TorsionSequence_shortExact_of_glueingPair
    (φ : R →+* S) (f : R) (X : Pullback φ f)
    (hpair : IsBeauvilleLaszloGlueingPairAlong φ f) :
    (h0TorsionSequence φ f X).ShortExact := sorry

namespace BaseChange

variable [Algebra R S]

/-- 15.91.16.3: for a Beauville--Laszlo glueing pair, the base-changed
mod-torsion sequence is short exact. -/
@[stacks 0BP5 "base-changed single-principal-open mod-torsion short exact sequence"]
theorem sequence_shortExact_of_glueingPair
    (f : R) (X : Pullback (R := R) (S := S) f)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R S) f) :
    (sequence f X).ShortExact := sorry

end BaseChange

end LocalizedModule.Away.FormalGluing.Single
