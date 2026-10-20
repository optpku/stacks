/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Polynomial.Evaluation
public import ReasLib.RingTheory.MvPolynomial.LinearApproximation

/-!
# Completed evaluation of I-adic polynomials

Evaluation and shifted evaluation of `A[x_ι]^∧` in an `I`-adically complete
`A`-algebra.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

#check (Algebra.NaiveCotangent.Adic.X :
  ∀ {A ι : Type u} [CommRing A] (I : Ideal A) (i : ι), polynomialCompletion A I ι)

#check (Algebra.NaiveCotangent.Adic.adicAeval :
  ∀ {A ι C : Type u} [CommRing A] [CommRing C] [Algebra A C] (I : Ideal A)
    [IsAdicComplete (I.map (algebraMap A C)) C] (v : ι → C),
    polynomialCompletion A I ι →ₐ[A] C)

#check (Algebra.NaiveCotangent.Adic.aevalShift :
  ∀ {A ι C : Type u} [CommRing A] [CommRing C] [Algebra A C] {I : Ideal A}
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C),
    polynomialCompletion A I ι →ₐ[A] C)
