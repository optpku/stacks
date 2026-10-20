/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section

universe u v

namespace Algebra.FiniteType

/-- A finite-type algebra over a Jacobson commutative ring is Jacobson. -/
theorem isJacobsonRing
    (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsJacobsonRing A] [Algebra.FiniteType A B] : IsJacobsonRing B := sorry

/-- A non-nilpotent element of a finite-type algebra over a field avoids some maximal ideal. -/
theorem exists_isMaximal_notMem_of_not_isNilpotent
    (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] {f : R} (hf : ¬ IsNilpotent f) :
    ∃ m : Ideal R, m.IsMaximal ∧ f ∉ m :=
  sorry

end Algebra.FiniteType

namespace MvPolynomial

/-- A radical ideal in a finite-variable polynomial ring over a Jacobson ring equals its Jacobson radical. -/
theorem eq_jacobson_of_isRadical
    {R : Type u} [CommRing R] [IsJacobsonRing R] {ι : Type v} [Finite ι]
    {I : Ideal (MvPolynomial ι R)} (hI : I.IsRadical) : I = I.jacobson :=
  sorry

end MvPolynomial
