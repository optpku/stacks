/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineComparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- 70.5.10.1: specialize to `X = X_i`, the affine scheme `U = U_i`, and
`A = O_{X_i}(X_i)`, with its canonical morphism `p : X_i ⟶ Spec(A_i)`.
The descended polynomials `g` define `B_i`, and the chosen sections `h` satisfying
these relations define `U_i ⟶ Spec(B_i)` by quotient evaluation. This is the
displayed commutative diagram; cartesianness is a later deduction. -/
@[stacks 084U]
#check (AlgebraicGeometry.AlgebraicSpace.AffineComparison.quotientEvaluation_commSq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} {A : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (p : X ⟶ ofOver (Over.mk σA)) (f : ofOver U ⟶ X)
    {n : ℕ} (g : Fin n → MvPolynomial (Fin n) A)
    (h : Fin n → Scheme.Γ.obj (Opposite.op U.left))
    (hrel : ∀ k, MvPolynomial.eval₂ (AffineComparison.coefficientMap σA p f).hom h (g k) = 0),
    CommSq f (AlgebraicGeometry.AlgebraicSpace.ofOverMap
      (AffineComparison.quotientSpecOverMap σA p f g h hrel)) p
      (AlgebraicGeometry.AlgebraicSpace.ofOverHomMk
        (Spec.map (AffineComparison.quotientMap g)) rfl))

