/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: SelmerGroup.lean:476-476, SelmerGroup.lean:1024-1049.
Changes: extracted arithmetic dependency layers, narrowed imports, and documented ownership.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import ReasLib.RingTheory.DedekindDomain.SelmerGroup.Finiteness
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Number-field specializations of S-unit rank and Selmer finiteness

The carrier stays Mathlib's Selmer subgroup for `R = 𝓞 F`. Dirichlet's theorem
and the class number theorem supply the two finiteness hypotheses. The exponent
remains arbitrary and nonzero. See `audits/selmer/NumberFieldExample.lean` for an
actual call at exponent two and a finite set of primes, including finite support of
the prime valuations of specified nonzero elements. No square-class alias is added.
-/

@[expose] public section

namespace IsDedekindDomain

section NumberField

open NumberField

variable (F : Type*) [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ)

/-- **Dirichlet's unit theorem**, `Group.FG` version: the unit group of the ring of integers of
a number field is finitely generated. -/
instance instGroupFGUnitsRingOfIntegers : Group.FG (𝓞 F)ˣ :=
  Group.fg_iff_monoid_fg.mpr inferInstance

/-- The Selmer group `K(S,n)` of a number field is finite for `S` finite and `n ≠ 0`. -/
theorem finite_selmerGroup_of_numberField [NeZero n] (hS : S.Finite) :
    Finite (selmerGroup (K := F) (S := S) (n := n)) :=
  finite_selmerGroup (𝓞 F) F S n hS

open Module in
/-- **Dirichlet's `S`-unit theorem** for number fields, rank version: the group of `S`-units of
a number field `F` has rank `rank F + |S|`, where `rank F = r₁ + r₂ - 1` is the unit rank. -/
theorem finrank_sUnit_of_numberField (hS : S.Finite) :
    finrank ℤ (Additive (S.unit F)) = NumberField.Units.rank F + S.ncard := by
  rw [finrank_sUnit F S hS, NumberField.Units.finrank_eq]

end NumberField

end IsDedekindDomain

end
