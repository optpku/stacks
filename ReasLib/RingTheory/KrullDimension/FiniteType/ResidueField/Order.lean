/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Transcendence.FiniteType
public import ReasLib.RingTheory.KrullDimension.FiniteType.ResidueField

/-!
# Order of residue-field transcendence degrees

For a finite-type algebra over a field, residue-field transcendence degree is strictly antitone on
the prime spectrum. The ideal-level statement used by the chapter is exposed as a thin bridge to
this point-level order API.

@stack 06RP
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

variable {k : Type u} [Field k] {S : Type v} [CommRing S]
  [Algebra k S] [Algebra.FiniteType k S]

/-- Residue-field transcendence degree is strictly antitone along prime inclusions in a finite-type
algebra over a field. -/
@[stacks 06RP "point form"]
theorem trdeg_residueField_strictAnti :
    StrictAnti (fun p : PrimeSpectrum S =>
      Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField)) := by
  intro p q hpq
  have hq_top : Order.coheight q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hq_eq := Algebra.FiniteType.residueField_trdegToNat_eq_coheight
      (k := k) q.asIdeal
    have hq_eq' :
        (↑(Cardinal.toNat (Algebra.trdeg k q.asIdeal.ResidueField)) : WithBot ℕ∞) = ⊤ := by
      simpa [htop] using hq_eq
    exact ENat.coe_ne_top _ (WithBot.coe_eq_top.mp hq_eq')
  have hcoheight := Order.coheight_strictAnti hpq hq_top
  have hcoheight' :
      (↑(Order.coheight q) : WithBot ℕ∞) <
        (↑(Order.coheight p) : WithBot ℕ∞) :=
    WithBot.coe_lt_coe.mpr hcoheight
  rw [← Algebra.FiniteType.residueField_trdegToNat_eq_coheight
      (k := k) q.asIdeal,
    ← Algebra.FiniteType.residueField_trdegToNat_eq_coheight
      (k := k) p.asIdeal] at hcoheight'
  simpa using hcoheight'

end PrimeSpectrum

namespace Algebra.FiniteType

variable {k : Type u} [Field k] {S : Type v} [CommRing S]
  [Algebra k S] [Algebra.FiniteType k S]

/-- Lemma 10.116.2 (Stacks `06RP`): if `q < q'` are prime ideals in a finite-type algebra over a
field, then the transcendence degree of `q'.ResidueField` is strictly smaller than that of
`q.ResidueField`. -/
@[stacks 06RP]
theorem trdeg_residueField_lt_of_lt
    (q q' : Ideal S) [q.IsPrime] [q'.IsPrime] (hqq' : q < q') :
    Cardinal.toNat (Algebra.trdeg k q'.ResidueField) <
      Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
  let p : PrimeSpectrum S := ⟨q, inferInstance⟩
  let p' : PrimeSpectrum S := ⟨q', inferInstance⟩
  have hp : p < p' := by
    change q < q'
    exact hqq'
  have h := PrimeSpectrum.trdeg_residueField_strictAnti (k := k) hp
  simpa [p, p'] using h

/-- The cardinal-valued form of `trdeg_residueField_lt_of_lt`. Finite type makes both
transcendence degrees finite, so the natural-number comparison reflects back to cardinals. -/
@[stacks 06RP "cardinal form"]
theorem trdeg_residueField_lt_of_lt_cardinal
    (q q' : Ideal S) [q.IsPrime] [q'.IsPrime] (hqq' : q < q') :
    Algebra.trdeg k q'.ResidueField < Algebra.trdeg k q.ResidueField := by
  -- Local instance justification: finite type of `S/k` makes both residue fields
  -- essentially finite type, which is needed only to reflect `toNat` inequalities.
  letI : Algebra.EssFiniteType k q.ResidueField :=
    Algebra.EssFiniteType.comp k S q.ResidueField
  letI : Algebra.EssFiniteType k q'.ResidueField :=
    Algebra.EssFiniteType.comp k S q'.ResidueField
  have hq : Algebra.trdeg k q.ResidueField < Cardinal.aleph0 :=
    Algebra.trdeg_lt_aleph0_of_essFiniteType (K := k) (L := q.ResidueField)
  have hq' : Algebra.trdeg k q'.ResidueField < Cardinal.aleph0 :=
    Algebra.trdeg_lt_aleph0_of_essFiniteType (K := k) (L := q'.ResidueField)
  exact
    (Cardinal.toNat_lt_iff_lt_of_lt_aleph0 hq' hq).mp
      (trdeg_residueField_lt_of_lt (k := k) q q' hqq')

end Algebra.FiniteType
