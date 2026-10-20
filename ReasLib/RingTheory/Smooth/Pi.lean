/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Pi
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Smoothness of Finite Products

The formal-smoothness and finite-presentation components of `Algebra.Smooth`
are both stable under finite products.  The finite-family theorem is the
canonical owner; the binary product form is a convenient specialization.

@stack 0GIF
-/

universe u v w

namespace Algebra.Smooth

section Pi

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Finite ι] {A : ι → Type w}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

/-- Lemma 10.137.14, tag `0GIF`: a finite product of commutative `R`-algebras
is smooth exactly when each factor is smooth. -/
@[stacks 0GIF "smoothness of finite products"]
theorem pi_iff :
    Algebra.Smooth R ((i : ι) → A i) ↔ ∀ i, Algebra.Smooth R (A i) := sorry

end Pi

section Prod

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Lemma 10.137.14, tag `0GIF`: a binary product of commutative `R`-algebras
is smooth exactly when both factors are smooth. -/
@[stacks 0GIF "smoothness of binary products"]
theorem prod_iff :
    Algebra.Smooth R (S × T) ↔ Algebra.Smooth R S ∧ Algebra.Smooth R T := sorry

end Prod

end Algebra.Smooth
