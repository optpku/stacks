/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Tensor.Principal

/-!
# `Tor` of Ideal Quotients

This leaf relates the first `Tor` group of an ideal quotient to injectivity of
the canonical ideal tensor multiplication map. It deliberately exposes only
the proposition-level consequence: a concrete quotient-kernel equivalence
requires a separately constructed low-degree boundary.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The first `Tor` of `M` with `R ⧸ I` vanishes exactly when ideal tensor
multiplication by `I` on `M` is injective. -/
@[stacks 00M6 "Tor of an ideal quotient"]
theorem isZero_oneQuotient_iff (I : Ideal R) :
    IsZero (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R (R ⧸ I))) ↔
      Function.Injective (I.tensorMul M) := sorry

/-- A zero kernel for ideal tensor multiplication implies vanishing of the first `Tor`
with the corresponding ideal quotient. -/
@[stacks 00M6 "Tor of an ideal quotient"]
theorem isZero_oneQuotient_of_ker_eq_bot (I : Ideal R)
    (hker : LinearMap.ker (I.tensorMul M) = ⊥) :
    IsZero (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R (R ⧸ I))) := sorry

/-- Stacks 00M6: if `f` is regular on `M`, then the first `Tor` of `M` with
the principal quotient `R ⧸ (f)` vanishes. -/
@[stacks 00M6 "Tor of a principal ideal quotient"]
theorem isZero_oneQuotient_span_singleton {f : R}
    (hf : IsSMulRegular M f) :
    IsZero (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R (R ⧸ Ideal.span ({f} : Set R)))) := sorry

end CategoryTheory.ModuleCat.Tor
