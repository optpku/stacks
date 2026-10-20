/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

/-!
# Krull Dimension of Finite-Type Domains over a Field

This leaf relates the Krull dimension of a finite-type domain over a field to its
transcendence degree.  The result is stated for the algebra itself, rather than for a chosen
normalization or fraction-field presentation, so it can be used uniformly by dimension and
residue-field arguments.
-/

namespace Algebra.FiniteType

universe u v

/-- A finite-type domain over a field has Krull dimension equal to the natural-number
transcendence degree over the base field.

The finite-type hypothesis is essential: this equality does not extend to arbitrary essentially
finite type algebras, whose localizations can have a different Krull dimension. -/
theorem ringKrullDim_eq_trdeg
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toNat (Algebra.trdeg k A) : WithBot ℕ∞) := sorry

end Algebra.FiniteType
