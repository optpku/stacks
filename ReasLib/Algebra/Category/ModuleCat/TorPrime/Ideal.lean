module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Tensor

/-!
# `Tor'` of Ideal Quotients

This leaf records the ideal-quotient criterion for mathlib's alternative
`Tor'` convention, derived in the first variable. It deliberately exposes a
proposition-level vanishing criterion rather than a chosen quotient-kernel
equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ModuleCat.Tor'

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Stacks 00M6: the first `Tor'` of `M` with `R ⧸ I` vanishes exactly when ideal tensor
multiplication by `I` on `M` is injective. -/
@[stacks 00M6 "Tor of an ideal quotient"]
theorem isZero_oneQuotient_iff (I : Ideal R) :
    IsZero (((CategoryTheory.Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R (R ⧸ I))) ↔
      Function.Injective (I.tensorMul M) := sorry

end CategoryTheory.ModuleCat.Tor'
