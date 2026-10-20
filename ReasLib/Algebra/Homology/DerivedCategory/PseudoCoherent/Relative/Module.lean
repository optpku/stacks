/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Module
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Presentation
public import ReasLib.Algebra.Module.FinitePresentation.Relative.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative pseudo-coherence for modules

This leaf gives the module-level forms of the presentationwise relative
pseudo-coherence API.  It avoids requiring applications to pass through the
degree-zero cochain complex explicitly.

@stack 0675
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.ModuleCat

/-- Relative `m`-pseudo-coherence of a module is equivalent to absolute `m`-pseudo-coherence
after restriction along every surjective finite polynomial presentation. -/
@[stacks 065I "module relative m-pseudo-coherence over every presentation"]
theorem isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : ModuleCat A) (m : ℤ) :
    M.IsMPseudoCoherentRelativeTo R m ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
        ((ModuleCat.restrictScalars α.toRingHom).obj M).IsMPseudoCoherent m := sorry

/-- Relative `m`-pseudo-coherence of a module can be checked after restriction along one
surjective finite polynomial presentation. -/
@[stacks 065I "module relative m-pseudo-coherence over some presentation"]
theorem isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : ModuleCat A) (m : ℤ) :
    M.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
        ((ModuleCat.restrictScalars α.toRingHom).obj M).IsMPseudoCoherent m := sorry

/-- Relative pseudo-coherence of a module is equivalent to absolute pseudo-coherence after
restriction along every surjective finite polynomial presentation. -/
@[stacks 065I "module relative pseudo-coherence over every presentation"]
theorem isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : ModuleCat A) :
    M.IsPseudoCoherentRelativeTo R ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
        ((ModuleCat.restrictScalars α.toRingHom).obj M).IsPseudoCoherent := sorry

/-- Relative pseudo-coherence of a module can be checked after restriction along one
surjective finite polynomial presentation. -/
@[stacks 065I "module relative pseudo-coherence over some presentation"]
theorem isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : ModuleCat A) :
    M.IsPseudoCoherentRelativeTo R ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
        ((ModuleCat.restrictScalars α.toRingHom).obj M).IsPseudoCoherent := sorry

end CategoryTheory.ModuleCat

namespace CategoryTheory.Module

/-- Relative `m`-pseudo-coherence of an ordinary module is equivalent to absolute
`m`-pseudo-coherence after restriction along every surjective finite polynomial presentation. -/
@[stacks 065I "ordinary-module relative m-pseudo-coherence over every presentation"]
theorem isMPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [AddCommGroup M] [Module A M] (m : ℤ) :
    Module.IsMPseudoCoherentRelativeTo R A M m ↔
      ∀ n : ℕ,
        ∀ (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
          ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A M)).IsMPseudoCoherent m := sorry

/-- Relative `m`-pseudo-coherence of an ordinary module can be checked after restriction along
one surjective finite polynomial presentation. -/
@[stacks 065I "ordinary-module relative m-pseudo-coherence over some presentation"]
theorem isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [AddCommGroup M] [Module A M] (m : ℤ) :
    Module.IsMPseudoCoherentRelativeTo R A M m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
        ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A M)).IsMPseudoCoherent m := sorry

/-- Relative pseudo-coherence of an ordinary module is equivalent to absolute pseudo-coherence
after restriction along every surjective finite polynomial presentation. -/
@[stacks 065I "ordinary-module relative pseudo-coherence over every presentation"]
theorem isPseudoCoherentRelativeTo_iff_overEveryPolynomialPresentation
    {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [AddCommGroup M] [Module A M] :
    Module.IsPseudoCoherentRelativeTo R A M ↔
      ∀ n : ℕ,
        ∀ (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
          ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A M)).IsPseudoCoherent := sorry

/-- Relative pseudo-coherence of an ordinary module can be checked after restriction along one
surjective finite polynomial presentation. -/
@[stacks 065I "ordinary-module relative pseudo-coherence over some presentation"]
theorem isPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} {A : Type v} {M : Type w} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [AddCommGroup M] [Module A M] :
    Module.IsPseudoCoherentRelativeTo R A M ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
        ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A M)).IsPseudoCoherent := sorry

end CategoryTheory.Module

namespace CategoryTheory.Module.IsMPseudoCoherentRelativeTo

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable [AddCommGroup M] [Module A M]

/-- Lemma 15.82.7 (1): relative `0`-pseudo-coherence is equivalent to finite generation. -/
@[stacks 0675 "(1), finite module criterion"]
theorem zero_iff_finite :
    Module.IsMPseudoCoherentRelativeTo R A M 0 ↔ Module.Finite A M := sorry

/-- Lemma 15.82.7 (2): relative `(-1)`-pseudo-coherence is equivalent to relative finite
presentation. -/
@[stacks 0675 "(2), finite presentation criterion"]
theorem minusOne_iff_finitePresentationRelativeTo :
    Module.IsMPseudoCoherentRelativeTo R A M (-1) ↔
      Module.FinitePresentationRelativeTo R A M := sorry

/-- Lemma 15.82.7 (3): relative `(-d)`-pseudo-coherence is equivalent to a length-`d` finite
free resolution after restriction along every polynomial presentation. -/
@[stacks 0675 "(3), finite free resolution criterion"]
theorem neg_iff_hasLengthFiniteFreeResolutionRelativeTo (d : ℕ) :
    Module.IsMPseudoCoherentRelativeTo R A M (-(d : ℤ)) ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          Module.HasLengthFiniteFreeResolution P M d := sorry

end CategoryTheory.Module.IsMPseudoCoherentRelativeTo

namespace CategoryTheory.Module.IsPseudoCoherentRelativeTo

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable [AddCommGroup M] [Module A M]

/-- Lemma 15.82.7 (4): relative pseudo-coherence is equivalent to an infinite finite-free
resolution after restriction along every polynomial presentation. -/
@[stacks 0675 "(4), infinite finite free resolution criterion"]
theorem iff_hasFiniteFreeResolutionRelativeTo :
    Module.IsPseudoCoherentRelativeTo R A M ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          ∃ (F : ChainComplex (ModuleCat P) ℕ)
            (π : F ⟶ ChainComplex.moduleSingle P (ModuleCat.of P M)),
            ChainComplex.IsFiniteFreeResolution π := sorry

end CategoryTheory.Module.IsPseudoCoherentRelativeTo
