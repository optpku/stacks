/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness descent along injective integral maps

This leaf records flatness descent for modules finitely presented over a polynomial algebra.

@stack 0534
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.Flat.Integral

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

/-- Lemma 15.21.6: let `R ⟶ S` be an injective integral map and let `M` be finitely presented
over `MvPolynomial (Fin n) R`. If its scalar extension to `S` is flat over `S`, then `M` is flat
after restricting scalars to `R`. -/
@[stacks 0534 "Lemma 15.21.6"]
theorem of_finitePresentation_mvPolynomial
    (n : ℕ) {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M]
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S
      (S ⊗[R] RestrictScalars R (MvPolynomial (Fin n) R) M)) :
    Module.Flat R (RestrictScalars R (MvPolynomial (Fin n) R) M) := sorry

end Module.Flat.Integral
