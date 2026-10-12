/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import ReasLib.NumberTheory.FunctionField.Adele

/-!
# Unramified adelic GL₂ cusp forms

Functions `GL (Fin 2) A → Λ` that are right `GL (Fin 2) K`-invariant, left
`GL (Fin 2) O`-invariant, and have vanishing unipotent sums over `A / K`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix
open Finset

noncomputable section

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type v} [Ring Λ]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- Right invariance under `GL (Fin 2) K`. -/
def IsRightInvariant (f : GL (Fin 2) (adeleRing X) → Λ) : Prop :=
  ∀ x γ, f (x * functionFieldGL X γ) = f x

/-- Unfold right `K`-invariance of an adelic function. -/
theorem isRightInvariant_iff (f : GL (Fin 2) (adeleRing X) → Λ) :
    IsRightInvariant X f ↔ ∀ x γ, f (x * functionFieldGL X γ) = f x := sorry

/-- Left invariance under `GL (Fin 2) O`. -/
def IsLeftInvariant (f : GL (Fin 2) (adeleRing X) → Λ) : Prop :=
  ∀ u x, f (integerAdeleGL X u * x) = f x

/-- Unfold left `O`-invariance of an adelic function. -/
theorem isLeftInvariant_iff (f : GL (Fin 2) (adeleRing X) → Λ) :
    IsLeftInvariant X f ↔ ∀ u x, f (integerAdeleGL X u * x) = f x := sorry

/-- A finite set `s` is a complete set of representatives for the quotient `A / U`. -/
def IsCompleteReps {A : Type u} [AddGroup A] (U : AddSubgroup A) (s : Finset A) : Prop :=
  ∀ a : A, ∃! b : A, b ∈ s ∧ a - b ∈ U

/-- Unfold the complete-representatives condition. -/
theorem isCompleteReps_iff {A : Type u} [AddGroup A] (U : AddSubgroup A) (s : Finset A) :
    IsCompleteReps U s ↔ ∀ a : A, ∃! b : A, b ∈ s ∧ a - b ∈ U := sorry

/-- Cuspidality: the unipotent integrand is locally constant and its finite sums
over complete representatives of `A / (K + U)` vanish. -/
def IsCuspidal (f : GL (Fin 2) (adeleRing X) → Λ) : Prop :=
  ∀ x, ∃ (U : AddSubgroup (adeleRing X)) (s : Finset (adeleRing X)),
    (∀ z, ∀ u ∈ U,
      f (x * GeneralLinearGroup.upperRightHom (z + u)) =
        f (x * GeneralLinearGroup.upperRightHom z)) ∧
      IsCompleteReps (principalAdeles X ⊔ U) s ∧
      ∑ a ∈ s, f (x * GeneralLinearGroup.upperRightHom a) = 0

/-- Unfold cuspidality into local constancy, complete representatives, and vanishing sums. -/
theorem isCuspidal_iff (f : GL (Fin 2) (adeleRing X) → Λ) :
    IsCuspidal X f ↔
      ∀ x, ∃ (U : AddSubgroup (adeleRing X)) (s : Finset (adeleRing X)),
        (∀ z, ∀ u ∈ U,
          f (x * GeneralLinearGroup.upperRightHom (z + u)) =
            f (x * GeneralLinearGroup.upperRightHom z)) ∧
          IsCompleteReps (principalAdeles X ⊔ U) s ∧
          ∑ a ∈ s, f (x * GeneralLinearGroup.upperRightHom a) = 0 := sorry

/-- An unramified cusp form on `GL (Fin 2) A` with values in `Λ`. -/
structure UnramifiedCuspForm (Λ : Type v) [Ring Λ] [Fintype k]
    [Invertible (ringChar k : Λ)] where
  /-- The underlying function `GL (Fin 2) A → Λ`. -/
  toFun : GL (Fin 2) (adeleRing X) → Λ
  /-- Right invariance under `GL (Fin 2) K`. -/
  right_inv : IsRightInvariant X toFun
  /-- Left invariance under `GL (Fin 2) O`. -/
  left_inv : IsLeftInvariant X toFun
  /-- Vanishing of unipotent integrals over `A / K`. -/
  cuspidal : IsCuspidal X toFun

namespace UnramifiedCuspForm

variable [Fintype k] [Invertible (ringChar k : Λ)]

/-- Build an unramified cusp form from a function satisfying right invariance,
left invariance, and cuspidality. -/
def of (f : GL (Fin 2) (adeleRing X) → Λ)
    (h_right : IsRightInvariant X f) (h_left : IsLeftInvariant X f)
    (h_cusp : IsCuspidal X f) : UnramifiedCuspForm X Λ where
  toFun := f
  right_inv := h_right
  left_inv := h_left
  cuspidal := h_cusp

/-- An unramified cusp form is right `K`-invariant, left `O`-invariant, and cuspidal. -/
theorem spec (f : UnramifiedCuspForm X Λ) :
    IsRightInvariant X f.toFun ∧ IsLeftInvariant X f.toFun ∧ IsCuspidal X f.toFun := sorry

/-- The zero unramified cusp form. -/
protected def zero : UnramifiedCuspForm X Λ where
  toFun := fun _ ↦ 0
  right_inv := sorry
  left_inv := sorry
  cuspidal := sorry

/-- The underlying function of the zero form is the zero function. -/
theorem zero_toFun :
    (UnramifiedCuspForm.zero X : UnramifiedCuspForm X Λ).toFun = fun _ ↦ (0 : Λ) := sorry

/-- Unramified cusp forms are equal if their underlying functions agree. -/
theorem ext (f g : UnramifiedCuspForm X Λ) (h : f.toFun = g.toFun) : f = g := sorry

end UnramifiedCuspForm

end AlgebraicGeometry.SchemeOverField
