/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometric reducedness of polynomial algebras

The polynomial closure of geometric reducedness is intrinsic to the
`Algebra.IsGeometricallyReduced` predicate.  The statement is made over an
arbitrary commutative base ring; the field-only tensor-product criterion is a
consumer-specific specialization and is not part of this owner.

@stack 04KN
-/

@[expose] public section

universe u v

namespace Algebra.IsGeometricallyReduced

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Lemma 10.43.3 (Tag 04KN): a polynomial algebra over a geometrically reduced algebra is
geometrically reduced over the same base ring.  The theorem is also the canonical typeclass
instance, so consumers can use either `polynomial` explicitly or ordinary instance search. -/
@[stacks 04KN, instance]
theorem polynomial [IsGeometricallyReduced R A] :
    IsGeometricallyReduced R (Polynomial A) := sorry

/-- Explicit-hypothesis form of `polynomial`; use this when geometric reducedness is available
as a proposition value rather than an installed instance. -/
@[stacks 04KN "explicit polynomial closure bridge"]
theorem polynomial_of (hA : IsGeometricallyReduced R A) :
    IsGeometricallyReduced R (Polynomial A) := sorry

end Algebra.IsGeometricallyReduced
