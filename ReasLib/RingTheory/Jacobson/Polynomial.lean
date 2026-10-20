/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Jacobson.Idempotent
public import ReasLib.RingTheory.ReesAlgebra.Integral.Idempotent
public import Mathlib.RingTheory.Ideal.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial witnesses over Jacobson ideals

@stack 0EM0

A product decomposition of the closed fiber of a finite algebra yields a monic polynomial
relation with a prescribed reduction over a Zariski pair.
-/

@[expose] public section

open Polynomial

universe u v w w'

namespace Algebra

variable {A : Type u} {B : Type v} {B₁ : Type w} {B₂ : Type w'}
variable [CommRing A] [CommRing B] [CommRing B₁] [CommRing B₂]
variable [Algebra A B] [Module.Finite A B]
variable (I : Ideal A)
variable [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]

/-- Lemma 15.10.4 (Stacks `0EM0`): over a Zariski pair, an element selecting the first
factor of a closed-fiber product decomposition satisfies a monic equation reducing to
`(X - 1) * X ^ d` for some positive `d`. -/
@[stacks 0EM0]
theorem exists_monic_polynomial_of_product_decomposition_mod_ideal
    (hI : I ≤ Ring.jacobson A)
    (hprod : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A ⧸ I] (B₁ × B₂))
    (hsurj : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B)
    (hb : hprod (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) =
      ((1 : B₁), (0 : B₂))) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
      f.Monic ∧ aeval b f = 0 ∧
        f.map (Ideal.Quotient.mk I) = ((X - 1) * X ^ d : (A ⧸ I)[X]) := sorry

end Algebra
