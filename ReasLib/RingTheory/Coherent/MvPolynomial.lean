/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import ReasLib.RingTheory.Coherent.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import ReasLib.RingTheory.Ideal.BaseChange
import ReasLib.RingTheory.MvPolynomial.FiniteVariables
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of multivariate polynomial rings

Coherence of a multivariate polynomial ring can be checked on its finite-variable polynomial
subrings. In particular, polynomial rings in arbitrarily many variables over a Noetherian ring
are coherent.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- Coherence of all finite-variable polynomial subrings implies coherence of the full
multivariate polynomial ring. -/
@[stacks 01BX "finite-variable coherence criterion"]
theorem isCoherentRing_of_finiteVariables
    {σ : Type u} {R : Type v} [CommRing R]
    (h : ∀ s : Finset σ, IsCoherentRing (MvPolynomial s R)) :
    IsCoherentRing (MvPolynomial σ R) := sorry

/-- A multivariate polynomial ring over a Noetherian commutative ring is coherent. -/
theorem isCoherentRing_of_noetherian
    {σ : Type u} {R : Type v} [CommRing R] [IsNoetherianRing R] :
    IsCoherentRing (MvPolynomial σ R) := sorry

/-- A multivariate polynomial ring in an arbitrary type of variables over a Noetherian ring is
coherent. -/
@[stacks 01BX "Noetherian coefficient ring"]
instance (priority := 900) isCoherentRing
    {σ : Type u} {R : Type v} [CommRing R] [IsNoetherianRing R] :
    IsCoherentRing (MvPolynomial σ R) := isCoherentRing_of_noetherian

end MvPolynomial
