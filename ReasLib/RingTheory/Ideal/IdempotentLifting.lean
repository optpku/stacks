/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import ReasLib.Algebra.Group.Idempotent
public import ReasLib.RingTheory.Ideal.IdempotentLifting.Correction
public import ReasLib.RingTheory.Ideal.LocallyNilpotent.Idempotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Idempotent lifting along ideals

This module aggregates reusable idempotent-lifting APIs.  Its commutative-algebra
predicates say that reduction modulo an ideal lifts idempotents after finite or
integral algebra extensions; the child leaves separately own nilpotent-element
correction and locally nilpotent quotient lifting.  These are properties of the
mathematics, rather than of a particular Chapter 15 presentation of henselian pairs.

@stack 09XI
-/

@[expose] public section

universe u v

section

variable {A : Type u} [CommRing A]

namespace Ideal

/-- Reduction modulo the extension of `I` lifts idempotents for every finite `A`-algebra. -/
@[stacks 09XI "finite-algebra idempotent lifting criterion"]
def HasFiniteAlgebraIdempotentLifting (I : Ideal A) : Prop :=
  ∀ ⦃B : Type (max u v)⦄ [CommRing B] [Algebra A B] [Module.Finite A B],
    Function.Bijective (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)).idempotentMap

/-- The finite-algebra idempotent-lifting property includes the identity `A`-algebra. -/
@[stacks 09XI "idempotents modulo a henselian ideal"]
theorem HasFiniteAlgebraIdempotentLifting.bijective_idempotentMap {I : Ideal A}
    (hI : I.HasFiniteAlgebraIdempotentLifting) :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := sorry

/-- Reduction modulo the extension of `I` lifts idempotents for every integral `A`-algebra. -/
@[stacks 09XI "integral-algebra idempotent lifting criterion"]
def HasIntegralAlgebraIdempotentLifting (I : Ideal A) : Prop :=
  ∀ ⦃B : Type (max u v)⦄ [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Function.Bijective (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)).idempotentMap

end Ideal

end
