/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Data.Complex.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Lifting

/-!
# Characteristic-zero comparisons for projective space

This file records characteristic-zero liftability of standard projective spaces,
the associated function-field degree comparisons, and a common complex lift.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Standard projective space over a field lifts to characteristic zero in every
dimension. -/
theorem liftsToCharZero_projectiveSpace {k : Type u} [Field k] (n : ℕ) :
    liftsToCharZero (ProjectiveSpace.schemeOver k n) := sorry

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.ProjectiveSpace

/-- The induced function-field degree of a dominant projective-line endomorphism
is unchanged by base change from a characteristic-zero domain to a field. -/
theorem inducedFunctionFieldDegree_eq_of_charZeroBaseChange
    {R k : Type u} [CommRing R] [IsDomain R] [CharZero R] [Field k]
    (φ : R →+* k) (π : schemeOver R 1 ⟶ schemeOver R 1)
    [IsIntegral (schemeOver R 1).left] [IsDominant π.left]
    [IsIntegral ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      (schemeOver R 1)).left]
    [IsDominant ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π).left] :
    ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π).left.inducedFunctionFieldDegree =
      π.left.inducedFunctionFieldDegree := sorry

/-- The induced function-field degree of a dominant projective-line endomorphism
is unchanged after base change to `ULift ℂ`. -/
theorem inducedFunctionFieldDegree_eq_of_complexBaseChange
    {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    (φ : R →+* ULift.{u} ℂ) (π : schemeOver R 1 ⟶ schemeOver R 1)
    [IsIntegral (schemeOver R 1).left] [IsDominant π.left]
    [IsIntegral ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      (schemeOver R 1)).left]
    [IsDominant ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π).left] :
    ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π).left.inducedFunctionFieldDegree =
      π.left.inducedFunctionFieldDegree := inducedFunctionFieldDegree_eq_of_charZeroBaseChange φ π

/-- A dominant projective-line endomorphism over a finite field has a common
characteristic-zero model and a complex specialization preserving its degree. -/
theorem exists_complexLift {k : Type u} [Field k] [Finite k]
    (π : schemeOver k 1 ⟶ schemeOver k 1)
    [IsIntegral (schemeOver k 1).left] [IsDominant π.left] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : CharZero R)
      (φ : R →+* k) (ψ : R →+* ULift.{u} ℂ)
      (πR : schemeOver R 1 ⟶ schemeOver R 1)
      (πC : schemeOver (ULift.{u} ℂ) 1 ⟶ schemeOver (ULift.{u} ℂ) 1)
      (ek : (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj
        (schemeOver R 1) ≅ schemeOver k 1)
      (eC : (Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj
        (schemeOver R 1) ≅ schemeOver (ULift.{u} ℂ) 1)
      (h_complex_integral : IsIntegral (schemeOver (ULift.{u} ℂ) 1).left)
      (h_complex_dominant : IsDominant πC.left),
      (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map πR ≫ ek.hom =
        ek.hom ≫ π ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom ψ))).map πR ≫ eC.hom =
        eC.hom ≫ πC ∧
      -- Local instance justification (proof-local temporary data): Install the existentially supplied integrality proof only to elaborate inducedFunctionFieldDegree.
      letI : IsIntegral (schemeOver (ULift.{u} ℂ) 1).left := h_complex_integral
      -- Local instance justification (proof-local temporary data): Install the existentially supplied dominance proof only to elaborate inducedFunctionFieldDegree.
      letI : IsDominant πC.left := h_complex_dominant
      πC.left.inducedFunctionFieldDegree = π.left.inducedFunctionFieldDegree := sorry

end AlgebraicGeometry.ProjectiveSpace
