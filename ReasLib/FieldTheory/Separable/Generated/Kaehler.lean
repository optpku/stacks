/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.FormallySmooth
public import ReasLib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kähler criteria for Stacks-separable field extensions

This leaf turns the field-level formal-smoothness criterion for
`Algebra.IsSeparableOver` into reusable Jacobi-Zariski consequences.

@stack 031X
@stack 0322
-/

@[expose] public section

universe u v w

namespace Algebra.IsSeparableOver

variable {R : Type u} {k : Type v} {K : Type w}
variable [CommRing R] [Field k] [Field K]
variable [Algebra R k] [Algebra R K] [Algebra k K] [IsScalarTower R k K]

/-- Generalized owner for Lemma 10.158.4 (Tag `031X`): a Stacks-separable field
extension makes every Jacobi-Zariski Kähler base-change map in a scalar tower injective.
The source-facing prime-field positive-characteristic map is exposed by the `CharP` leaf. -/
@[stacks 031X]
theorem mapBaseChange_injective [Algebra.IsSeparableOver k K] :
    Function.Injective (KaehlerDifferential.mapBaseChange R k K) := sorry

/-- Explicit-hypothesis form of `mapBaseChange_injective`; use this when separability is
available as a proposition value rather than an installed instance. -/
@[stacks 031X "explicit hypothesis bridge"]
theorem mapBaseChange_injective_of
    (hsep : Algebra.IsSeparableOver k K) :
    Function.Injective (KaehlerDifferential.mapBaseChange R k K) := sorry

/-- Generalized owner for Proposition 10.158.9 (5), tag `0322`: over a
characteristic-zero field, every Kähler base-change map for a scalar tower `R → k → K` is
injective.  The source's `R = ℤ` specialization is the chapter recall. -/
@[stacks 0322 "(5)"]
theorem mapBaseChange_injective_of_charZero [CharZero k] :
    Function.Injective (KaehlerDifferential.mapBaseChange R k K) := sorry

end Algebra.IsSeparableOver
