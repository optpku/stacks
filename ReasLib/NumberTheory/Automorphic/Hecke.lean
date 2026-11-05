/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.NumberTheory.Automorphic.CuspForms
public import ReasLib.NumberTheory.FunctionField.LocalAdele
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints

/-! # Hecke operators on fixed-character cusp forms -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix

noncomputable section

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {Λ : Type v} [CommRing Λ] [Invertible (ringChar k : Λ)]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- A local uniformizer obtained by completing a valuation-one function-field element. -/
def uniformizer (place : closedPoints X.left) : (completion X place)ˣ :=
  let parameter := Classical.choose
    ((SchemeOverField.place X place).valuation_exists_uniformizer X.left.functionField)
  Units.mk0 (parameter : completion X place) (by
    apply (Valuation.ne_zero_iff
      (Valued.v : Valuation (completion X place) (WithZero (Multiplicative ℤ)))).mp
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
    exact ne_of_eq_of_ne (Classical.choose_spec
      ((SchemeOverField.place X place).valuation_exists_uniformizer X.left.functionField))
      WithZero.coe_ne_zero)

omit [Fintype k] [Projective X.hom] [GeometricallyIrreducible X.hom] in
/-- The chosen local parameter has valuation `exp (-1)`. -/
theorem uniformizer_isUniformizer (place : closedPoints X.left) :
    IsUniformizer X place (uniformizer X place).val := by
  change Valued.v ((Classical.choose
    ((SchemeOverField.place X place).valuation_exists_uniformizer X.left.functionField) :
      X.left.functionField) : completion X place) = WithZero.exp (-1 : ℤ)
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
  exact Classical.choose_spec
    ((SchemeOverField.place X place).valuation_exists_uniformizer X.left.functionField)

/-- A stalk-valued section of the residue map at a closed point. -/
def residueSection (place : closedPoints X.left)
    (residue : X.left.residueField place.1) : X.left.presheaf.stalk place.1 :=
  Classical.choose
    (IsLocalRing.residue_surjective (R := X.left.presheaf.stalk place.1) residue)

/-- The residue of the chosen stalk representative is the original residue class. -/
theorem residue_residueSection (place : closedPoints X.left)
    (residue : X.left.residueField place.1) :
    IsLocalRing.residue (X.left.presheaf.stalk place.1) (residueSection X place residue) =
      residue := sorry

/-- The image of the residue section in the completed local integers. -/
def residueSectionIntegers (place : closedPoints X.left)
    (residue : X.left.residueField place.1) : completionIntegers X place :=
  algebraMap (X.left.presheaf.stalk place.1) (completionIntegers X place)
    (residueSection X place residue)

/-- The completed residue representative is the algebra map of its stalk representative. -/
theorem residueSectionIntegers_apply (place : closedPoints X.left)
    (residue : X.left.residueField place.1) :
    residueSectionIntegers X place residue =
      algebraMap (X.left.presheaf.stalk place.1) (completionIntegers X place)
        (residueSection X place residue) := sorry

omit [Fintype k] in
/-- The diagonal matrices with entries `(π⁻¹, 1)` and `(π, 1)` are mutual inverses. -/
theorem heckeDiag_inverse (place : closedPoints X.left) (parameter : (completion X place)ˣ) :
    Matrix.diagonal (fun index : Fin 2 ↦ if index = 0 then parameter.inv else 1) *
        Matrix.diagonal (fun index : Fin 2 ↦ if index = 0 then parameter.val else 1) = 1 ∧
      Matrix.diagonal (fun index : Fin 2 ↦ if index = 0 then parameter.val else 1) *
        Matrix.diagonal (fun index : Fin 2 ↦ if index = 0 then parameter.inv else 1) = 1 := sorry

omit [Fintype k] in
/-- The diagonal local Hecke representative with entries `(π⁻¹, 1)`. -/
def heckeDiag (place : closedPoints X.left) (parameter : (completion X place)ˣ) :
    GL (Fin 2) (completion X place) where
  val := Matrix.diagonal fun index ↦ if index = 0 then parameter.inv else 1
  inv := Matrix.diagonal fun index ↦ if index = 0 then parameter.val else 1
  val_inv := (heckeDiag_inverse X place parameter).1
  inv_val := (heckeDiag_inverse X place parameter).2

omit [Fintype k] in
/-- The lower-triangular matrices with rows `(1, 0), (-π⁻¹r, π⁻¹)` and
`(1, 0), (r, π)` are mutual inverses. -/
theorem heckeUnip_inverse (place : closedPoints X.left) (parameter : (completion X place)ˣ)
    (representative : completion X place) :
    !![1, 0; -parameter.inv * representative, parameter.inv] *
        !![1, 0; representative, parameter.val] = 1 ∧
      !![1, 0; representative, parameter.val] *
        !![1, 0; -parameter.inv * representative, parameter.inv] = 1 := sorry

omit [Fintype k] in
/-- The lower-triangular local Hecke representative with rows `(1, 0), (-π⁻¹r, π⁻¹)`. -/
def heckeUnip (place : closedPoints X.left) (parameter : (completion X place)ˣ)
    (representative : completion X place) : GL (Fin 2) (completion X place) where
  val := !![1, 0; -parameter.inv * representative, parameter.inv]
  inv := !![1, 0; representative, parameter.val]
  val_inv := (heckeUnip_inverse X place parameter representative).1
  inv_val := (heckeUnip_inverse X place parameter representative).2

namespace CuspForms

variable {X}

/-- The Hecke finite sum consists of a diagonal translation and all residue-indexed
lower-triangular translations. -/
def heckeT_toFun (character : closedPoints X.left → Λˣ) (place : closedPoints X.left)
    (form : CuspForms X Λ character) (point : GL (Fin 2) (adeleRing X)) : Λ :=
  form.toFun (localGL X place (heckeDiag X place (uniformizer X place)) * point) +
    ∑ residue : X.left.residueField place.1,
      form.toFun (localGL X place (heckeUnip X place (uniformizer X place)
        (residueSectionIntegers X place residue)) * point)

/-- The Hecke finite sum preserves invariance, cuspidality, and the fixed central character. -/
theorem heckeT_mem (character : closedPoints X.left → Λˣ) (place : closedPoints X.left)
    (form : CuspForms X Λ character) :
    heckeT_toFun character place form ∈ cuspFormsSubmodule X Λ character := sorry

/-- The Hecke finite-sum formula respects addition and coefficient scalar multiplication. -/
theorem heckeT_linear (character : closedPoints X.left → Λˣ) (place : closedPoints X.left) :
    (∀ first second : CuspForms X Λ character,
      heckeT_toFun character place (first + second) =
        heckeT_toFun character place first + heckeT_toFun character place second) ∧
      (∀ (scalar : Λ) (form : CuspForms X Λ character),
        heckeT_toFun character place (scalar • form) =
          scalar • heckeT_toFun character place form) := sorry

/-- The linear Hecke endomorphism given by the diagonal and lower-triangular finite sum. -/
def heckeT (character : closedPoints X.left → Λˣ) (place : closedPoints X.left) :
    Module.End Λ (CuspForms X Λ character) where
  toFun form := ⟨heckeT_toFun character place form, heckeT_mem character place form⟩
  map_add' := fun first second ↦ Subtype.ext ((heckeT_linear character place).1 first second)
  map_smul' := fun scalar form ↦ Subtype.ext ((heckeT_linear character place).2 scalar form)

/-- Evaluation of the Hecke endomorphism is its chosen-representative finite-sum formula. -/
theorem heckeT_apply (character : closedPoints X.left → Λˣ) (place : closedPoints X.left)
    (form : CuspForms X Λ character) (point : GL (Fin 2) (adeleRing X)) :
    (heckeT character place form).toFun point = heckeT_toFun character place form point := sorry

/-- The Hecke finite-sum formula holds for every uniformizer and every stalk-valued
right inverse of the residue map, independently of these choices. -/
theorem heckeT_apply_of_choices (character : closedPoints X.left → Λˣ)
    (place : closedPoints X.left) (parameter : (completion X place)ˣ)
    (h_parameter : IsUniformizer X place parameter.val)
    (sectionMap : X.left.residueField place.1 → X.left.presheaf.stalk place.1)
    (h_section : Function.RightInverse sectionMap
      (IsLocalRing.residue (X.left.presheaf.stalk place.1)))
    (form : CuspForms X Λ character) (point : GL (Fin 2) (adeleRing X)) :
    (heckeT character place form).toFun point =
      form.toFun (localGL X place (heckeDiag X place parameter) * point) +
        ∑ residue : X.left.residueField place.1,
          form.toFun (localGL X place (heckeUnip X place parameter
            (algebraMap (X.left.presheaf.stalk place.1) (completionIntegers X place)
              (sectionMap residue))) * point) := sorry

set_option synthInstance.maxHeartbeats 200000 in
/-- The central Hecke endomorphism is inverse-character scaling of the identity. -/
def heckeU (character : closedPoints X.left → Λˣ) (place : closedPoints X.left) :
    Module.End Λ (CuspForms X Λ character) :=
  SMul.smul (character place).inv (LinearMap.id : Module.End Λ (CuspForms X Λ character))

/-- The central Hecke endomorphism acts by the inverse prescribed character value. -/
theorem heckeU_apply (character : closedPoints X.left → Λˣ) (place : closedPoints X.left)
    (form : CuspForms X Λ character) :
    heckeU character place form = (character place)⁻¹ • form := sorry

end CuspForms

end AlgebraicGeometry.SchemeOverField
