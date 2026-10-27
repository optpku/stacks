/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Cover
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open Algebra.TensorProduct
open scoped TensorProduct

universe u

open CechCrisCover

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (c : CechCrisCover x₀)

/-- Polynomial algebra `P_idx` attached to a covering member. -/
abbrev CechCrisCover.polynomial (idx : c.Λ) : Type u :=
  MvPolynomial (c.vars idx) A

/-- The degree-zero polynomial stage is the chosen polynomial ring; each successor tensors the first factor with the tail. -/
noncomputable def CechCrisCover.simplexPolynomialStage
    (c : CechCrisCover x₀) : (n : ℕ) → (Fin (n + 1) → c.Λ) → CommAlgCat A
  | 0, σ => CommAlgCat.of A (c.polynomial (σ 0))
  | n + 1, σ => CommAlgCat.of A
      (TensorProduct A (c.polynomial (σ 0))
        (CechCrisCover.simplexPolynomialStage c n (fun i => σ i.succ)))

/-- The carrier of the recursively defined tensor polynomial algebra. -/
abbrev CechCrisCover.simplexPolynomial (n : ℕ) (σ : Fin (n + 1) → c.Λ) : Type u :=
  c.simplexPolynomialStage n σ

/-- The ring structure on the recursive polynomial carrier comes from its algebra bundle. -/
def CechCrisCover.simplexPolynomial.commRing (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    CommRing (c.simplexPolynomial n σ) := (c.simplexPolynomialStage n σ).commRing

/-- The base scalar action on the recursive polynomial carrier comes from its algebra bundle. -/
def CechCrisCover.simplexPolynomial.algebra (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Algebra A (c.simplexPolynomial n σ) := (c.simplexPolynomialStage n σ).algebra

/-- Inclusion of a covering-member polynomial algebra as a tensor factor of `P_σ`. -/
public noncomputable def CechCrisCover.simplexPolynomialSlot
    (c : CechCrisCover x₀) (n : ℕ) (σ : Fin (n + 1) → c.Λ) (i : Fin (n + 1)) :
    c.polynomial (σ i) →ₐ[A] c.simplexPolynomial n σ :=
  match n, σ, i with
  | 0, σ, i =>
      Fin.cases (AlgHom.id A (c.polynomial (σ 0))) (fun j => j.elim0) i
  | n + 1, σ, i =>
      let previous := CechCrisCover.simplexPolynomialStage c n (fun j => σ j.succ)
      Fin.cases
        (includeLeft (R := A) (S := A) (A := c.polynomial (σ 0))
          (B := previous))
        (fun j0 =>
          (includeRight (R := A) (A := c.polynomial (σ 0))
            (B := previous)).comp
            (CechCrisCover.simplexPolynomialSlot c n (fun j => σ j.succ) j0))
        i

/-- The unique factor of a degree-zero tensor polynomial algebra is the identity. -/
public theorem CechCrisCover.simplexPolynomialSlot_zero (σ : Fin 1 → c.Λ) :
    CechCrisCover.simplexPolynomialSlot c 0 σ 0 = AlgHom.id A (c.polynomial (σ 0)) :=
  rfl

/-- Algebra map `P_{σ ∘ f} → P_σ` from the trivial cosimplicial structure on polynomial
presentations. -/
public noncomputable def CechCrisCover.simplexPolynomialMap
    (c : CechCrisCover x₀) (n m : ℕ) (f : Fin (n + 1) → Fin (m + 1))
    (σ : Fin (m + 1) → c.Λ) :
    c.simplexPolynomial n (fun i => σ (f i)) →ₐ[A] c.simplexPolynomial m σ :=
  match n, f with
  | 0, f =>
      CechCrisCover.simplexPolynomialSlot c m σ (f 0)
  | n + 1, f =>
      let previous :=
        CechCrisCover.simplexPolynomialStage c n (fun i => σ (f i.succ))
      Algebra.TensorProduct.productMap
        (CechCrisCover.simplexPolynomialSlot c m σ (f 0))
        (CechCrisCover.simplexPolynomialMap c n m (fun i => f i.succ) σ)

/-- In degree zero the polynomial comparison is the corresponding tensor slot. -/
public theorem CechCrisCover.simplexPolynomialMap_zero
    (m : ℕ) (f : Fin 1 → Fin (m + 1)) (σ : Fin (m + 1) → c.Λ) :
    c.simplexPolynomialMap 0 m f σ = c.simplexPolynomialSlot m σ (f 0) :=
  rfl


/-- Canonical algebra map `P_{idx_0…idx_n} → Γ(X, U_{idx_0…idx_n})` induced by the
presentations and open restrictions. -/
noncomputable def CechCrisCover.simplexSurjection
    (c : CechCrisCover x₀) :
    (n : ℕ) → (σ : Fin (n + 1) → c.Λ) →
      c.simplexPolynomial n σ →ₐ[A] c.simplexRing n σ
  | 0, σ =>
      { toRingHom :=
          (restriction (le_of_eq (c.simplexOpen_zero σ))).comp (c.π (σ 0))
        commutes' := sorry }
  | n + 1, σ =>
      let previous := CechCrisCover.simplexPolynomialStage c n (fun i => σ i.succ)
      Algebra.TensorProduct.productMap
        { toRingHom :=
            (restriction (c.simplexOpen_le_member (n + 1) σ 0)).comp (c.π (σ 0))
          commutes' := sorry }
        { toRingHom :=
            (restriction (c.simplexOpen_succ_le n σ)).comp
              (CechCrisCover.simplexSurjection c n (fun i => σ i.succ)).toRingHom
          commutes' := sorry }

/-- Kernel `J_{idx_0…idx_n}` of the canonical surjection from the tensor polynomial algebra. -/
noncomputable def CechCrisCover.simplexKernel (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Ideal (c.simplexPolynomial n σ) :=
  RingHom.ker (c.simplexSurjection n σ).toRingHom

/-- The simplex polynomial algebra in degree `0` is `P_{σ 0}`. -/
theorem CechCrisCover.simplexPolynomial_zero (σ : Fin 1 → c.Λ) :
    c.simplexPolynomial 0 σ = c.polynomial (σ 0) :=
  rfl

/-- The canonical map in degree `0` is the chosen presentation, restricted to the
simplex open. -/
theorem CechCrisCover.simplexSurjection_zero (σ : Fin 1 → c.Λ) :
    (c.simplexSurjection 0 σ).toRingHom =
      (restriction (le_of_eq (c.simplexOpen_zero σ))).comp (c.π (σ 0)) :=
  rfl

/-- Each tensor presentation is surjective onto the simplex coordinate ring. -/
theorem CechCrisCover.simplexPolynomial_surjective (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Function.Surjective (c.simplexSurjection n σ) :=
  sorry

/-- The kernel unfolds as the kernel of the tensor presentation. -/
theorem CechCrisCover.simplexKernel_eq (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    c.simplexKernel n σ = RingHom.ker (c.simplexSurjection n σ).toRingHom :=
  rfl

/-- Image of `I` in a simplex polynomial algebra is contained in the kernel. -/
theorem CechCrisCover.simplexIdeal_le_kernel (hI : Affine.idealCompatible IA I) (n : ℕ) (σ : Fin (n + 1) → c.Λ) :
    Ideal.map (algebraMap A (c.simplexPolynomial n σ)) IA ≤ c.simplexKernel n σ :=
  sorry


end
