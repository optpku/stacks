module

public import Mathlib.Algebra.Module.Submodule.Defs
public import ReasLib.NumberTheory.FunctionField.LocalAdele
public import ReasLib.NumberTheory.Automorphic.CuspForm

/-! # Unramified cusp forms with fixed central character -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix

noncomputable section

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {Λ : Type v} [CommRing Λ] [Invertible (ringChar k : Λ)]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- The central-character condition requires every inverse uniformizer translation to act
by the inverse prescribed character value. -/
def IsUEigen (function : GL (Fin 2) (adeleRing X) → Λ)
    (character : closedPoints X.left → Λˣ) : Prop :=
  ∀ (place : closedPoints X.left) (parameter : (completion X place)ˣ),
    IsUniformizer X place parameter.val →
      ∀ point, function (GeneralLinearGroup.scalar (Fin 2)
        (localAdeleUnit X place parameter)⁻¹ * point) = (character place)⁻¹ • function point

/-- The central-character condition quantifies over all local uniformizers. -/
theorem isUEigen_iff (function : GL (Fin 2) (adeleRing X) → Λ)
    (character : closedPoints X.left → Λˣ) :
    IsUEigen X function character ↔
      ∀ (place : closedPoints X.left) (parameter : (completion X place)ˣ),
        IsUniformizer X place parameter.val →
          ∀ point, function (GeneralLinearGroup.scalar (Fin 2)
            (localAdeleUnit X place parameter)⁻¹ * point) =
              (character place)⁻¹ • function point := sorry

/-- The zero function is invariant, cuspidal, and satisfies every fixed central character. -/
theorem cuspForms_zero (character : closedPoints X.left → Λˣ) :
    IsRightInvariant X (0 : GL (Fin 2) (adeleRing X) → Λ) ∧
      IsLeftInvariant X (0 : GL (Fin 2) (adeleRing X) → Λ) ∧
      IsCuspidal X (0 : GL (Fin 2) (adeleRing X) → Λ) ∧
      IsUEigen X (0 : GL (Fin 2) (adeleRing X) → Λ) character := sorry

/-- The defining conditions of fixed-character cusp forms are preserved by addition. -/
theorem cuspForms_add (character : closedPoints X.left → Λˣ)
    (first second : GL (Fin 2) (adeleRing X) → Λ)
    (h_first : IsRightInvariant X first ∧ IsLeftInvariant X first ∧
      IsCuspidal X first ∧ IsUEigen X first character)
    (h_second : IsRightInvariant X second ∧ IsLeftInvariant X second ∧
      IsCuspidal X second ∧ IsUEigen X second character) :
    IsRightInvariant X (first + second) ∧ IsLeftInvariant X (first + second) ∧
      IsCuspidal X (first + second) ∧ IsUEigen X (first + second) character := sorry

/-- The defining conditions of fixed-character cusp forms are preserved by coefficient scaling. -/
theorem cuspForms_smul (character : closedPoints X.left → Λˣ) (scalar : Λ)
    (function : GL (Fin 2) (adeleRing X) → Λ)
    (h_function : IsRightInvariant X function ∧ IsLeftInvariant X function ∧
      IsCuspidal X function ∧ IsUEigen X function character) :
    IsRightInvariant X (scalar • function) ∧ IsLeftInvariant X (scalar • function) ∧
      IsCuspidal X (scalar • function) ∧ IsUEigen X (scalar • function) character := sorry

/-- The submodule of invariant cuspidal adelic functions with a fixed central character. -/
def cuspFormsSubmodule (Λ : Type v) [CommRing Λ] [Invertible (ringChar k : Λ)]
    (character : closedPoints X.left → Λˣ) :
    Submodule Λ (GL (Fin 2) (adeleRing X) → Λ) where
  carrier := {function | IsRightInvariant X function ∧ IsLeftInvariant X function ∧
    IsCuspidal X function ∧ IsUEigen X function character}
  zero_mem' := cuspForms_zero X character
  add_mem' := fun h_first h_second ↦ cuspForms_add X character _ _ h_first h_second
  smul_mem' := fun scalar _ h_function ↦ cuspForms_smul X character scalar _ h_function

/-- Fixed-character cusp forms are the carrier of the invariant cuspidal submodule. -/
abbrev CuspForms (Λ : Type v) [CommRing Λ] [Invertible (ringChar k : Λ)]
    (character : closedPoints X.left → Λˣ) : Type _ :=
  cuspFormsSubmodule X Λ character

namespace CuspForms

variable {X}

/-- The underlying adelic function of a fixed-character cusp form. -/
def toFun {character : closedPoints X.left → Λˣ} (form : CuspForms X Λ character) :
    GL (Fin 2) (adeleRing X) → Λ :=
  form.val

/-- Construct a fixed-character cusp form from a function and its four defining conditions. -/
def of (character : closedPoints X.left → Λˣ) (function : GL (Fin 2) (adeleRing X) → Λ)
    (h_right : IsRightInvariant X function) (h_left : IsLeftInvariant X function)
    (h_cusp : IsCuspidal X function) (h_character : IsUEigen X function character) :
    CuspForms X Λ character :=
  ⟨function, h_right, h_left, h_cusp, h_character⟩

/-- The underlying function of the explicit constructor is the supplied function. -/
theorem of_toFun (character : closedPoints X.left → Λˣ)
    (function : GL (Fin 2) (adeleRing X) → Λ)
    (h_right : IsRightInvariant X function) (h_left : IsLeftInvariant X function)
    (h_cusp : IsCuspidal X function) (h_character : IsUEigen X function character) :
    (of character function h_right h_left h_cusp h_character).toFun = function := sorry

/-- A fixed-character cusp form satisfies right invariance, left invariance, cuspidality,
and the prescribed inverse-character eigenvalue condition. -/
theorem spec (character : closedPoints X.left → Λˣ) (form : CuspForms X Λ character) :
    IsRightInvariant X form.toFun ∧ IsLeftInvariant X form.toFun ∧
      IsCuspidal X form.toFun ∧ IsUEigen X form.toFun character := sorry

end CuspForms

end AlgebraicGeometry.SchemeOverField
