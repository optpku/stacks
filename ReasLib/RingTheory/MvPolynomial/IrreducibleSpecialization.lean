module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Irreducibility under specialization

This file provides a uniform irreducibility result for field-valued specializations of
multivariate polynomials over a suitable principal localization.
-/

@[expose] public section

universe u v w x

namespace MvPolynomial

/-- An absolutely irreducible multivariate polynomial over a domain remains irreducible after
every field-valued specialization from a suitable nonzero principal localization. -/
theorem exists_nonzero_away_irreducible_map
    {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {Kbar : Type w} [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    {n : ℕ} (P : MvPolynomial (Fin n) A)
    (hP : Irreducible (MvPolynomial.map ((algebraMap K Kbar).comp (algebraMap A K)) P)) :
    ∃ f : A, f ≠ 0 ∧ ∀ {κ : Type x} [Field κ] (φ : Localization.Away f →+* κ),
      Irreducible (MvPolynomial.map (φ.comp (algebraMap A (Localization.Away f))) P) := sorry

end MvPolynomial
