/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Laurent Polynomial N-1 Descent

This leaf records descent of the `N-1` condition from a one-variable Laurent
polynomial ring to its Noetherian domain of coefficients.
-/

universe u

open scoped LaurentPolynomial

namespace IsN1Ring

/-- Lemma 10.161.6, tag `032J`: if the one-variable Laurent polynomial ring
over a Noetherian domain is `N-1`, then the coefficient domain is `N-1`. -/
@[stacks 032J]
theorem of_laurentPolynomial
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsN1Ring R[T;T⁻¹]] :
    IsN1Ring R := sorry

end IsN1Ring
