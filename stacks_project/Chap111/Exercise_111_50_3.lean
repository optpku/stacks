/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Etale.SquarePresentation
import StacksCheckRecall

universe u v w

@[expose] public section

open MvPolynomial

/- Exercise 111.50.3: a square polynomial quotient with invertible Jacobian
determinant has a unique lift along each square-zero surjection of algebras. -/
@[stacks 02FE] #check (Algebra.SquarePresentation.existsUnique_lift :
  ∀ {R : Type u} {B' : Type v} {B : Type w} [CommRing R] [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B] (n : ℕ) (f : Fin n → MvPolynomial (Fin n) R)
    (hjac : IsUnit (Algebra.SquarePresentation.naive n f).jacobian) (π : B' →ₐ[R] B)
    (hπ : Function.Surjective π) (hker : (RingHom.ker π) ^ 2 = ⊥)
    (φ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] B),
    ∃! φ' : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] B',
      π.comp φ' = φ)
