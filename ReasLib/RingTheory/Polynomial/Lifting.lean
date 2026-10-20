/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Lifting monic polynomials

This leaf owns the coefficientwise lifting primitive.  Specializations for
quotients and residue maps should use this theorem instead of repeating the
`Polynomial.lifts` argument.
-/

namespace Polynomial

universe u v

/-- A surjective ring homomorphism lifts every monic polynomial to a monic
polynomial with the prescribed image. -/
theorem exists_monic_lift_of_surjective
    {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (g : Polynomial S) (hg : g.Monic) :
    ∃ p : Polynomial R, p.Monic ∧ p.map f = g := by
  obtain ⟨p, hpmap, _, hpmonic⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective (f := f) hf g) hg
  exact ⟨p, hpmonic, hpmap⟩

end Polynomial
