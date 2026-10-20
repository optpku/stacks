/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType
public import ReasLib.RingTheory.KrullDimension.Prime
public import ReasLib.RingTheory.LocalRing.ResidueField.Transcendence
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

/-!
# Residue fields of finite-type algebras

This leaf packages the dimension formulas for a prime quotient and its residue
field in a finite-type algebra over a field.  The APIs use prime ideals because
the quotient and residue-field constructions are both canonically owned by
`Ideal`; the coheight occurrence is the corresponding `PrimeSpectrum` point.
-/

namespace Algebra.FiniteType

universe u v

/-- For a prime ideal of a finite-type algebra over a field, the Krull dimension
of the prime quotient is the transcendence degree of its residue field. -/
theorem ringKrullDim_quotient_eq_trdeg_residueField
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime] :
    ringKrullDim (A ⧸ p) =
      (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) := sorry

/-- For a prime ideal of a finite-type algebra over a field, the transcendence
degree of its residue field is the coheight of the corresponding point. -/
theorem residueField_trdegToNat_eq_coheight
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime] :
    (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) =
      (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum A) : WithBot ℕ∞) := sorry

/-- A finite-type domain over a field has Krull dimension equal to the height
of a prime plus the transcendence degree of its residue field. -/
theorem ringKrullDim_eq_height_add_trdeg_residueField
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime] :
    ringKrullDim A =
      (p.height : WithBot ℕ∞) + Cardinal.toNat (Algebra.trdeg k p.ResidueField) := sorry

end Algebra.FiniteType
