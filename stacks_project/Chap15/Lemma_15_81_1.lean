/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.Presentation
import StacksCheckRecall

/-!
# Lemma 15.81.1

@stack 05GY
-/

@[expose] public section

universe u v w x

/-! # Lemma 15.81.1: presentation-independent relative finite presentation -/

/- Lemma 15.81.1 (1), tag `05GY`: the polynomial-presentation characterization. -/
@[stacks 05GY "every polynomial presentation"]
#check fun {R : Type u} {A : Type v} {M : Type w}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Algebra.FiniteType R A] ↦
  (Module.FinitePresentationRelativeTo.iff_overEveryPolynomialPresentation :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A)
        (_ : Function.Surjective α), Module.FinitePresentationAlong α.toRingHom M)

/- Lemma 15.81.1 (2), tag `05GY`: the finitely presented cover characterization. -/
@[stacks 05GY "every finitely presented cover"]
#check fun {R : Type u} {A : Type v} {M : Type w}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Algebra.FiniteType R A] ↦
  (Module.FinitePresentationRelativeTo.iff_overAnyFinitelyPresentedCover :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ (A' : Type x) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
        (f : A' →ₐ[R] A) (_ : Function.Surjective f),
          Module.FinitePresentationAlong f.toRingHom M)

/- Direct elimination APIs for a chosen polynomial presentation or cover. -/
#check @Module.FinitePresentationRelativeTo.overPolynomialPresentation
#check @Module.FinitePresentationRelativeTo.overAnyFinitelyPresentedCover
