/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic

/-!
# Quasi-regular quotients across locally nilpotent thickenings

This file owns the flatness and smoothness deformation theorems for quotients by finite
quasi-regular families.  The statements use canonical quotient rings and generated ideals
directly, independently of the prime-local proofs used to establish them.

@stack 0CEQ
@stack 0CER
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence.IsQuasiRegularSequence

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Module.Flat A B] [Algebra.FinitePresentation A B]

/-- Lemma 15.31.5, tag `0CEQ`: flatness of a quotient by a finite quasi-regular family deforms
across a locally nilpotent ideal of the base. -/
@[stacks 0CEQ "flat quasi-regular quotients across locally nilpotent thickenings"]
theorem flatQuotient_of_locallyNilpotent {I : Ideal A} {f : List B}
    (hqr : IsQuasiRegularSequence
      (f.map (Ideal.Quotient.mk (I.map (algebraMap A B)))))
    (hI : I.IsLocallyNilpotent)
    [Module.Flat (A ⧸ I)
      ((B ⧸ I.map (algebraMap A B)) ⧸
        Ideal.ofList (f.map (Ideal.Quotient.mk (I.map (algebraMap A B)))))] :
    Module.Flat A (B ⧸ Ideal.ofList f) := sorry

/-- Lemma 15.31.6, tag `0CER`: smoothness of a quotient by a finite quasi-regular family deforms
across a locally nilpotent ideal of the base. -/
@[stacks 0CER "smooth quasi-regular quotients across locally nilpotent thickenings"]
theorem smoothQuotient_of_locallyNilpotent {I : Ideal A} {f : List B}
    (hqr : IsQuasiRegularSequence
      (f.map (Ideal.Quotient.mk (I.map (algebraMap A B)))))
    (hI : I.IsLocallyNilpotent)
    [Algebra.Smooth (A ⧸ I)
      ((B ⧸ I.map (algebraMap A B)) ⧸
        Ideal.ofList (f.map (Ideal.Quotient.mk (I.map (algebraMap A B)))))] :
    Algebra.Smooth A (B ⧸ Ideal.ofList f) := sorry

end RingTheory.Sequence.IsQuasiRegularSequence
