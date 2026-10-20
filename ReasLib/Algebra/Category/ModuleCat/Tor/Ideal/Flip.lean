/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.TorPrime.Ideal
public import ReasLib.CategoryTheory.Monoidal.Tor

/-!
# First-Variable Ideal Quotients for `Tor`

@stack 00M6

This leaf records the quotient-first form of the degree-one ideal-quotient
criterion.  It is a proposition-level bridge: the existing `Tor'` criterion
and braided `Tor` symmetry supply the mathematical comparison, while no
additional quotient-kernel data is chosen here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Stacks 00M6: the degree-one ordinary `Tor` of `R ⧸ I` with `M` vanishes exactly when ideal
tensor multiplication on `M` is injective. This is the
quotient-first counterpart of `isZero_oneQuotient_iff`, transported through
`CategoryTheory.torFlipRightIso` from the first-derived `Tor'` convention. -/
@[stacks 00M6 "Tor of an ideal quotient (quotient first)"]
theorem isZero_oneQuotientFirst_iff (I : Ideal R) :
    IsZero (((CategoryTheory.Tor (ModuleCat R) 1).obj
      (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)) ↔
      Function.Injective (I.tensorMul M) := sorry

end CategoryTheory.ModuleCat.Tor
