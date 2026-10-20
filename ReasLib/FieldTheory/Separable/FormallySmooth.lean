/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated.Properties
public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental

/-!
# Formal smoothness and separability of field extensions

This leaf owns the field-extension bridges between Stacks-project
separability, formal smoothness, and first cotangent homology.  It is
independent of the Chapter 10 proof route through finite-adjoin direct limits.

@stack 031Y
@stack 031Z
@stack 0320
@stack 0321
@stack 0322
-/

@[expose] public section

universe u v

namespace Algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Lemma 10.158.5, tag `031Y`: a formally smooth field extension is
separable over its base in the Stacks-project sense. -/
@[stacks 031Y]
theorem isSeparableOver_of_formallySmooth [Algebra.FormallySmooth k K] :
    Algebra.IsSeparableOver k K := sorry

/-- Lemma 10.158.6, tag `031Z`: over a field, formal smoothness is equivalent
to the vanishing of first cotangent homology. -/
@[stacks 031Z]
theorem formallySmooth_iff_subsingleton_h1Cotangent_of_field :
    Algebra.FormallySmooth k K ↔ Subsingleton (Algebra.H1Cotangent k K) := sorry

/-- Lemma 10.158.7 (1), tag `0320`: a purely transcendental field extension
is formally smooth. -/
@[stacks 0320 "(1)"]
theorem formallySmooth_of_purelyTranscendental
    (hK : FieldExtension.IsPurelyTranscendental k K) :
    Algebra.FormallySmooth k K := sorry

/-- Lemma 10.158.7 (3), tag `0320`: a field extension separable over its
base in the Stacks-project sense is formally smooth. -/
@[stacks 0320 "(3)"]
theorem formallySmooth_of_isSeparableOver [Algebra.IsSeparableOver k K] :
    Algebra.FormallySmooth k K := sorry

/-- Proposition 10.158.9 (3), tag `0322`: every field extension of a
characteristic-zero field is formally smooth. -/
@[stacks 0322 "(3)"]
theorem formallySmooth_of_charZero [CharZero k] :
    Algebra.FormallySmooth k K := sorry

/-- Proposition 10.158.9 (4), tag `0322`: first cotangent homology of a
field extension over a characteristic-zero field is subsingleton. -/
@[stacks 0322 "(4)"]
theorem subsingleton_h1Cotangent_of_charZero [CharZero k] :
    Subsingleton (Algebra.H1Cotangent k K) := sorry

/-- Unrestricted companion to Lemma 10.158.8 (Tag `0321`): for field extensions,
formal smoothness is equivalent to separability over the base in the Stacks-project sense.
The source-facing positive-characteristic specialization is
`Algebra.FormallySmooth.CharP.iff_isSeparableOver`. -/
@[stacks 0321 "all-characteristic field-extension companion"]
theorem formallySmooth_iff_isSeparableOver :
    Algebra.FormallySmooth k K ↔ Algebra.IsSeparableOver k K := sorry

end Algebra

namespace Algebra.FormallySmooth.CharP

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- Lemma 10.158.8 (2), tag `0321`: in positive characteristic, formal
smoothness of a field extension is equivalent to separability over the base.
This source-facing specialization retains the characteristic hypothesis;
the unrestricted equivalence is `Algebra.formallySmooth_iff_isSeparableOver`.
-/
@[stacks 0321 "(2)"]
theorem iff_isSeparableOver :
    Algebra.FormallySmooth k K ↔ Algebra.IsSeparableOver k K := sorry

end Algebra.FormallySmooth.CharP
