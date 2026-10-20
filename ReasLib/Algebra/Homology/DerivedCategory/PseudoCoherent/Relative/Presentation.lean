/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial presentation criteria for relative pseudo-coherence

@stack 065H

The definitions are presentationwise.  This leaf exposes the interchangeable
``some presentation'' and ``every presentation'' forms needed by applications.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.CochainComplex

/-- Lemma 15.82.3 (1) (065H): relative `m`-pseudo-coherence can be checked on one surjective finite polynomial
presentation of the finite type algebra. -/
@[stacks 065H "complex relative m-pseudo-coherence over some presentation"]
theorem isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsMPseudoCoherent m := sorry

/-- Lemma 15.82.3 (2) (065H): relative pseudo-coherence is equivalent to absolute pseudo-coherence after restriction along
every surjective finite polynomial presentation. -/
@[stacks 065H "complex relative pseudo-coherence over every presentation"]
theorem isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : CochainComplex (ModuleCat A) ℤ) :
    K.IsPseudoCoherentRelativeTo R ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
        (K.polynomialPresentationRestriction α).IsPseudoCoherent := sorry

/-- The existence form of Lemma 15.82.3 (2): relative pseudo-coherence can be checked on one surjective finite polynomial presentation of
the finite type algebra. -/
@[stacks 065H "complex relative pseudo-coherence over some presentation"]
theorem isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : CochainComplex (ModuleCat A) ℤ) :
    K.IsPseudoCoherentRelativeTo R ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent := sorry

end CategoryTheory.CochainComplex
