/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Transport
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category

/-!
# Transport of divided powers on graded algebras

This leaf transports divided powers through the degreewise linear equivalence used to transport
the underlying nonnegative graded algebra.  The operations on even and positive-even direct sums
are explicit conjugates under `DirectSum.congrLinearEquiv`; the remaining fields are precisely the
divided-power laws.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v w

namespace NonnegGradedAlgebra.Transport

section DividedPowers

variable {R : Type u} [CommRing R]
variable (A : NonnegGradedAlgebra.{u, v} R)
variable {B : ℕ → Type w} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
variable (e : ∀ n, A.piece n ≃ₗ[R] B n)

/-- The linear equivalence on the direct sum of even homogeneous pieces induced by `e`. -/
def evenEquiv : A.evenPart ≃ₗ[R] (algebra A e).evenPart :=
  DirectSum.congrLinearEquiv fun d ↦ e (2 * d)

/-- The linear equivalence on the positive-even direct sum induced by `e`. -/
def evenPositiveEquiv : A.evenPositivePart ≃ₗ[R] (algebra A e).evenPositivePart :=
  DirectSum.congrLinearEquiv fun d ↦ e (2 * (d + 1))

/-- The linear equivalence on the direct sum of odd homogeneous pieces induced by `e`. -/
def oddEquiv : A.oddPart ≃ₗ[R] (algebra A e).oddPart :=
  DirectSum.congrLinearEquiv fun d ↦ e (2 * d + 1)

/-- The even-part equivalence acts on a homogeneous inclusion by the corresponding component of
`e`. -/
@[simp]
theorem evenEquiv_evenHom (d : ℕ) (x : A.piece (2 * d)) :
    evenEquiv A e (A.evenHom d x) =
      (algebra A e).evenHom d (e (2 * d) x) := sorry

/-- The positive-even equivalence acts on a homogeneous inclusion by the corresponding component
of `e`. -/
@[simp]
theorem evenPositiveEquiv_evenPositiveHom (d : ℕ)
    (x : A.piece (2 * (d + 1))) :
    evenPositiveEquiv A e (A.evenPositiveHom d x) =
      (algebra A e).evenPositiveHom d (e (2 * (d + 1)) x) := sorry

/-- The odd-part equivalence acts on a homogeneous inclusion by the corresponding component of
`e`. -/
@[simp]
theorem oddEquiv_oddHom (d : ℕ) (x : A.piece (2 * d + 1)) :
    oddEquiv A e (A.oddHom d x) =
      (algebra A e).oddHom d (e (2 * d + 1) x) := sorry

/-- The inverse even-part equivalence acts degreewise by `e.symm`. -/
@[simp]
theorem evenEquiv_symm_evenHom (d : ℕ) (x : (algebra A e).piece (2 * d)) :
    (evenEquiv A e).symm ((algebra A e).evenHom d x) =
      A.evenHom d ((e (2 * d)).symm x) := sorry

/-- The inverse positive-even equivalence acts degreewise by `e.symm`. -/
@[simp]
theorem evenPositiveEquiv_symm_evenPositiveHom (d : ℕ)
    (x : (algebra A e).piece (2 * (d + 1))) :
    (evenPositiveEquiv A e).symm ((algebra A e).evenPositiveHom d x) =
      A.evenPositiveHom d ((e (2 * (d + 1))).symm x) := sorry

/-- The inverse odd-part equivalence acts degreewise by `e.symm`. -/
@[simp]
theorem oddEquiv_symm_oddHom (d : ℕ) (x : (algebra A e).piece (2 * d + 1)) :
    (oddEquiv A e).symm ((algebra A e).oddHom d x) =
      A.oddHom d ((e (2 * d + 1)).symm x) := sorry

/-- Transport on even parts commutes with inclusion of the positive-even part. -/
theorem evenEquiv_evenPositiveToEven (x : A.evenPositivePart) :
    evenEquiv A e (A.evenPositiveToEven x) =
      (algebra A e).evenPositiveToEven (evenPositiveEquiv A e x) := sorry

/-- Transport on even parts preserves multiplication. -/
theorem evenEquiv_evenMul (x y : A.evenPart) :
    evenEquiv A e (A.evenMul x y) =
      (algebra A e).evenMul (evenEquiv A e x) (evenEquiv A e y) := sorry

/-- Transport preserves the action of the even part on the positive-even part. -/
theorem evenPositiveEquiv_evenMulPositive (x : A.evenPart) (y : A.evenPositivePart) :
    evenPositiveEquiv A e (A.evenMulPositive x y) =
      (algebra A e).evenMulPositive (evenEquiv A e x) (evenPositiveEquiv A e y) := sorry

/-- Transport preserves the action of the even part on the odd part. -/
theorem oddEquiv_evenMulOdd (x : A.evenPart) (y : A.oddPart) :
    oddEquiv A e (A.evenMulOdd x y) =
      (algebra A e).evenMulOdd (evenEquiv A e x) (oddEquiv A e y) := sorry

/-- Transport preserves multiplication of two odd direct-sum elements. -/
theorem evenPositiveEquiv_oddMul (x y : A.oddPart) :
    evenPositiveEquiv A e (A.oddMul x y) =
      (algebra A e).oddMul (oddEquiv A e x) (oddEquiv A e y) := sorry

/-- Transport on even parts preserves natural powers. -/
theorem evenEquiv_evenPow (x : A.evenPart) (n : ℕ) :
    evenEquiv A e (A.evenPow x n) = (algebra A e).evenPow (evenEquiv A e x) n := sorry

variable (gammaA : NonnegGradedAlgebra.DividedPowers A)

/-- The total divided-power family transported by conjugating with the even direct-sum
equivalences. -/
def gamma (n : ℕ) (x : (algebra A e).evenPositivePart) : (algebra A e).evenPart :=
  evenEquiv A e (gammaA n ((evenPositiveEquiv A e).symm x))

/-- The positive-index divided powers transported within the positive-even direct sum. -/
def gammaPos (n : ℕ+) (x : (algebra A e).evenPositivePart) :
    (algebra A e).evenPositivePart :=
  evenPositiveEquiv A e (gammaA.gammaPos n ((evenPositiveEquiv A e).symm x))

/-- The transported positive-index refinement agrees with the transported total operation. -/
theorem gamma_eq_gammaPos (n : ℕ+) (x : (algebra A e).evenPositivePart) :
    gamma A e gammaA n x =
      (algebra A e).evenPositiveToEven (gammaPos A e gammaA n x) := sorry

/-- Transported divided powers of a homogeneous input land in the forced homogeneous degree. -/
theorem gamma_degree (n d : ℕ) (x : (algebra A e).piece (2 * (d + 1))) :
    ∃ y : (algebra A e).piece (2 * (n * (d + 1))),
      gamma A e gammaA n ((algebra A e).evenPositiveHom d x) =
        (algebra A e).evenHom (n * (d + 1)) y := sorry

/-- The first transported divided power is the positive-even inclusion. -/
theorem gamma_one (x : (algebra A e).evenPositivePart) :
    gamma A e gammaA 1 x = (algebra A e).evenPositiveToEven x := sorry

/-- The zeroth transported divided power is the graded unit. -/
theorem gamma_zero (x : (algebra A e).evenPositivePart) :
    gamma A e gammaA 0 x = (algebra A e).oneEven := sorry

/-- Products of transported divided powers have the binomial coefficient prescribed by the
source divided powers. -/
theorem gamma_mul (n m : ℕ) (x : (algebra A e).evenPositivePart) :
    (algebra A e).evenMul (gamma A e gammaA n x) (gamma A e gammaA m x) =
      Nat.choose (n + m) n • gamma A e gammaA (n + m) x := sorry

/-- Transported divided powers are compatible with multiplication by arbitrary even elements. -/
theorem gamma_evenMul (n : ℕ) (x : (algebra A e).evenPart)
    (y : (algebra A e).evenPositivePart) :
    gamma A e gammaA n ((algebra A e).evenMulPositive x y) =
      (algebra A e).evenMul ((algebra A e).evenPow x n) (gamma A e gammaA n y) := sorry

/-- Higher transported divided powers vanish on products of odd homogeneous elements. -/
theorem gamma_oddMul {n : ℕ} (hn : 1 < n) (i j : ℕ)
    (x : (algebra A e).piece (2 * i + 1)) (y : (algebra A e).piece (2 * j + 1)) :
    gamma A e gammaA n ((algebra A e).oddMulTerm i j x y) = 0 := sorry

/-- Transported divided powers turn sums into the antidiagonal convolution. -/
theorem gamma_add (n : ℕ) (x y : (algebra A e).evenPositivePart) :
    gamma A e gammaA n (x + y) =
      (Finset.antidiagonal n).sum fun ij ↦
        (algebra A e).evenMul (gamma A e gammaA ij.1 x) (gamma A e gammaA ij.2 y) := sorry

/-- Iterated transported divided powers use the canonical `Nat.uniformBell` coefficient. -/
theorem gamma_comp (n : ℕ) (m : ℕ+) (x : (algebra A e).evenPositivePart) :
    gamma A e gammaA n (gammaPos A e gammaA m x) =
      Nat.uniformBell n m • gamma A e gammaA (n * (m : ℕ)) x := sorry

/-- The divided-power structure obtained by explicitly transporting `gammaA` through `e`. -/
@[stacks 09PQ "infrastructure: transport of graded divided powers"]
def dividedPowers : NonnegGradedAlgebra.DividedPowers (algebra A e) where
  gamma := gamma A e gammaA
  gammaPos := gammaPos A e gammaA
  gamma_eq_gammaPos := gamma_eq_gammaPos A e gammaA
  gamma_degree := gamma_degree A e gammaA
  gamma_one := gamma_one A e gammaA
  gamma_zero := gamma_zero A e gammaA
  gamma_mul := gamma_mul A e gammaA
  gamma_evenMul := gamma_evenMul A e gammaA
  gamma_oddMul := gamma_oddMul A e gammaA
  gamma_add := gamma_add A e gammaA
  gamma_comp := gamma_comp A e gammaA

/-- Evaluation of the transported divided powers is the explicit conjugated operation `gamma`. -/
@[simp]
theorem dividedPowers_apply (n : ℕ) (x : (algebra A e).evenPositivePart) :
    dividedPowers A e gammaA n x = gamma A e gammaA n x := sorry

/-- The positive-index field of the transported structure is the explicit conjugated operation
`gammaPos`. -/
@[simp]
theorem dividedPowers_gammaPos (n : ℕ+) (x : (algebra A e).evenPositivePart) :
    (dividedPowers A e gammaA).gammaPos n x = gammaPos A e gammaA n x := sorry

/-- On a transported homogeneous input, `gammaPiece` is transported degreewise from the source. -/
@[simp]
theorem dividedPowers_gammaPiece (n d : ℕ) (x : A.piece (2 * (d + 1))) :
    (dividedPowers A e gammaA).gammaPiece n d (e (2 * (d + 1)) x) =
      e (2 * (n * (d + 1))) (gammaA.gammaPiece n d x) := sorry

/-- The transported structure is uniquely characterized by compatibility with the even and
positive-even equivalences. -/
theorem dividedPowers_eq_of_map_gamma
    (delta : NonnegGradedAlgebra.DividedPowers (algebra A e))
    (hdelta : ∀ n x,
      evenEquiv A e (gammaA n x) = delta n (evenPositiveEquiv A e x)) :
    delta = dividedPowers A e gammaA := sorry

end DividedPowers

section Comparison

variable {R : Type u} [CommRing R]
variable (A : NonnegGradedAlgebra.{u, v} R)
variable {B : ℕ → Type v} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
variable (e : ∀ n, A.piece n ≃ₗ[R] B n)
variable (gammaA : NonnegGradedAlgebra.DividedPowers A)

/-- The even-part equivalence is the direct-sum map induced by the forward graded comparison. -/
theorem gradedHom_evenMap :
    (gradedHom A e).evenMap = (evenEquiv A e).toLinearMap := sorry

/-- The positive-even equivalence is the direct-sum map induced by the forward graded
comparison. -/
theorem gradedHom_evenPositiveMap :
    (gradedHom A e).evenPositiveMap = (evenPositiveEquiv A e).toLinearMap := sorry

/-- The forward graded comparison preserves the transported divided powers. -/
theorem hom_map_gamma (n : ℕ) (x : A.evenPositivePart) :
    (gradedHom A e).evenMap (gammaA n x) =
      dividedPowers A e gammaA n ((gradedHom A e).evenPositiveMap x) := sorry

/-- The canonical forward morphism from the source divided-power algebra to its transport. -/
def hom : NonnegGradedAlgebra.DividedPowers.Hom gammaA (dividedPowers A e gammaA) where
  toGradedHom := gradedHom A e
  map_gamma := hom_map_gamma A e gammaA

/-- The inverse graded comparison preserves the source divided powers. -/
theorem invHom_map_gamma (n : ℕ) (x : (algebra A e).evenPositivePart) :
    (gradedInvHom A e).evenMap (dividedPowers A e gammaA n x) =
      gammaA n ((gradedInvHom A e).evenPositiveMap x) := sorry

/-- The canonical inverse morphism from transported divided powers back to the source. -/
def invHom : NonnegGradedAlgebra.DividedPowers.Hom (dividedPowers A e gammaA) gammaA where
  toGradedHom := gradedInvHom A e
  map_gamma := invHom_map_gamma A e gammaA

/-- The forward divided-power comparison followed by its inverse is the identity. -/
theorem hom_comp_inv :
    NonnegGradedAlgebra.DividedPowers.Hom.comp (invHom A e gammaA) (hom A e gammaA) =
      NonnegGradedAlgebra.DividedPowers.Hom.id gammaA := sorry

/-- The inverse divided-power comparison followed by the forward map is the identity. -/
theorem inv_comp_hom :
    NonnegGradedAlgebra.DividedPowers.Hom.comp (hom A e gammaA) (invHom A e gammaA) =
      NonnegGradedAlgebra.DividedPowers.Hom.id (dividedPowers A e gammaA) := sorry

end Comparison

end NonnegGradedAlgebra.Transport

namespace DividedPowerGradedAlgebra

section Transport

variable {R : Type u} [CommRing R]
variable (A : DividedPowerGradedAlgebra.{u, v} R)
variable {B : ℕ → Type w} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
variable (e : ∀ n, A.toGradedAlgebra.piece n ≃ₗ[R] B n)

/-- A divided-power graded algebra transported to a degreewise linearly equivalent family. -/
@[stacks 09PQ "transported divided-power graded algebra"]
def transport : DividedPowerGradedAlgebra.{u, w} R :=
  of (NonnegGradedAlgebra.Transport.algebra A.toGradedAlgebra e)
    (NonnegGradedAlgebra.Transport.dividedPowers A.toGradedAlgebra e A.gamma)

end Transport

section Comparison

variable {R : Type u} [CommRing R]
variable (A : DividedPowerGradedAlgebra.{u, v} R)
variable {B : ℕ → Type v} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
variable (e : ∀ n, A.toGradedAlgebra.piece n ≃ₗ[R] B n)

/-- The forward transported divided-power morphism followed by its inverse is the identity. -/
theorem transport_hom_inv_id :
    NonnegGradedAlgebra.DividedPowers.Hom.comp
        (NonnegGradedAlgebra.Transport.invHom A.toGradedAlgebra e A.gamma)
        (NonnegGradedAlgebra.Transport.hom A.toGradedAlgebra e A.gamma) =
      NonnegGradedAlgebra.DividedPowers.Hom.id A.gamma := sorry

/-- The inverse transported divided-power morphism followed by the forward map is the identity. -/
theorem transport_inv_hom_id :
    NonnegGradedAlgebra.DividedPowers.Hom.comp
        (NonnegGradedAlgebra.Transport.hom A.toGradedAlgebra e A.gamma)
        (NonnegGradedAlgebra.Transport.invHom A.toGradedAlgebra e A.gamma) =
      NonnegGradedAlgebra.DividedPowers.Hom.id
        (NonnegGradedAlgebra.Transport.dividedPowers A.toGradedAlgebra e A.gamma) := sorry

/-- The canonical isomorphism from a divided-power graded algebra to its degreewise transport. -/
def transportIso : A ≅ transport A e where
  hom := NonnegGradedAlgebra.Transport.hom A.toGradedAlgebra e A.gamma
  inv := NonnegGradedAlgebra.Transport.invHom A.toGradedAlgebra e A.gamma
  hom_inv_id := transport_hom_inv_id A e
  inv_hom_id := transport_inv_hom_id A e

/-- The homogeneous map of the forward divided-power transport is the supplied equivalence. -/
@[simp]
theorem transportIso_hom_map (n : ℕ) :
    (transportIso A e).hom.toGradedHom.map n = (e n).toLinearMap := sorry

/-- The homogeneous map of the inverse divided-power transport is the inverse supplied
equivalence. -/
@[simp]
theorem transportIso_inv_map (n : ℕ) :
    (transportIso A e).inv.toGradedHom.map n = (e n).symm.toLinearMap := sorry

end Comparison

end DividedPowerGradedAlgebra
