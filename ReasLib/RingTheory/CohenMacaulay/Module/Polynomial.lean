/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module.Local

/-!
# Polynomial base change of locally Cohen--Macaulay modules

This leaf owns the finite-variable polynomial base-change theorem for a locally
Cohen--Macaulay module.  The variable type is an arbitrary finite type rather
than a presentation-specific `Fin n`; the latter is a chapter-facing
specialization.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.LocallyCohenMacaulay

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {σ : Type w} [Finite σ]

/-- A finite-variable polynomial base change of a locally Cohen--Macaulay
module remains locally Cohen--Macaulay.  The finite index type is left
abstract so the result can be reused for any finite presentation of the
polynomial ring.
-/
theorem mvPolynomial [Module.LocallyCohenMacaulay R M] :
    Module.LocallyCohenMacaulay (MvPolynomial σ R)
      ((MvPolynomial σ R) ⊗[R] M) := sorry

/-- Lemma 10.103.13 (Stacks tag `0AAI`): the source's natural-number-indexed
presentation is the `Fin n` specialization of the finite-variable polynomial
base-change theorem.
-/
@[stacks 0AAI]
theorem mvPolynomial_fin [Module.LocallyCohenMacaulay R M] (n : ℕ) :
    Module.LocallyCohenMacaulay (MvPolynomial (Fin n) R)
      ((MvPolynomial (Fin n) R) ⊗[R] M) := sorry

end Module.LocallyCohenMacaulay
