/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Perfect.Presentation
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

/-!
# Lemma 15.83.2 compatibility entry point

The polynomial-presentation criterion for perfect ring maps is owned by
`ReasLib.RingTheory.RingHom.Perfect.Presentation`.

@stack 068Y
-/

/- Lemma 15.83.2, tag `068Y`: the perfect polynomial-presentation criterion. -/
@[stacks 068Y "perfect polynomial presentation"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) =>
  (RingHom.isPerfectRingMap_iff_hasPerfectPolynomialPresentation f :
    f.IsPerfectRingMap ↔ f.HasPerfectPolynomialPresentation)

/- Algebra-map specialization with the presentation written explicitly. -/
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] =>
  (Algebra.isPerfectRingMap_iff_hasPerfectPolynomialPresentation (A := A) (B := B) :
    (algebraMap A B).IsPerfectRingMap ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
        let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
        (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect)
