/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ModuleEnd
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A four-dimensional exact two-periodic complex

This file constructs a two-periodic complex from two sparse endomorphisms of a
four-dimensional vector space and states its determinant formula.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.TwoPeriodicEndomorphism.FourByFour

variable {k : Type u} [Field k]

/-- The endomorphism with unit entries `u₁` in position `(1, 0)` and `u₂` in
position `(3, 2)`. -/
def phi (u₁ u₂ : kˣ) : Module.End k (Fin 4 → k) :=
  Matrix.toLin' !![0, 0, 0, 0;
                   u₁, 0, 0, 0;
                   0, 0, 0, 0;
                   0, 0, u₂, 0]

/-- The coordinate action of `phi`. -/
theorem phi_apply (u₁ u₂ : kˣ) (x : Fin 4 → k) :
    phi u₁ u₂ x = ![0, u₁ * x 0, 0, u₂ * x 2] := sorry

/-- The endomorphism with unit entries `v₂` in position `(1, 2)` and `v₁` in
position `(3, 0)`. -/
def psi (v₁ v₂ : kˣ) : Module.End k (Fin 4 → k) :=
  Matrix.toLin' !![0, 0, 0, 0;
                   0, 0, v₂, 0;
                   0, 0, 0, 0;
                   v₁, 0, 0, 0]

/-- The coordinate action of `psi`. -/
theorem psi_apply (v₁ v₂ : kˣ) (x : Fin 4 → k) :
    psi v₁ v₂ x = ![0, v₂ * x 2, 0, v₁ * x 0] := sorry

/-- The range of `phi` is the kernel of `psi`. -/
theorem phi_range_eq_psi_ker (u₁ u₂ v₁ v₂ : kˣ) :
    (phi u₁ u₂).range = (psi v₁ v₂).ker := sorry

/-- The range of `psi` is the kernel of `phi`. -/
theorem psi_range_eq_phi_ker (u₁ u₂ v₁ v₂ : kˣ) :
    (psi v₁ v₂).range = (phi u₁ u₂).ker := sorry

/-- The exact two-periodic complex carried by `phi` and `psi`. -/
def complex (u₁ u₂ v₁ v₂ : kˣ) :
    TwoPeriodicEndomorphism (ModuleCat k) :=
  ofModuleEnd (phi u₁ u₂) (psi v₁ v₂)
    (phi_range_eq_psi_ker u₁ u₂ v₁ v₂).le
    (psi_range_eq_phi_ker u₁ u₂ v₁ v₂).le

/-- The carrier of `complex` has finite length over `k`. -/
theorem complex_isFiniteLength (u₁ u₂ v₁ v₂ : kˣ) :
    IsFiniteLength k (complex u₁ u₂ v₁ v₂).X := sorry

/-- The two sparse differentials make `complex` acyclic. -/
theorem complex_acyclic (u₁ u₂ v₁ v₂ : kˣ) :
    (complex u₁ u₂ v₁ v₂).toCochainComplex.Acyclic := sorry

/-- The determinant of the exact four-dimensional two-periodic complex is the
residue-field image of `-(u₁ * u₂) / (v₁ * v₂)`. -/
theorem determinant_eq (u₁ u₂ v₁ v₂ : kˣ) :
    determinant (complex u₁ u₂ v₁ v₂)
        (complex_isFiniteLength u₁ u₂ v₁ v₂)
        (complex_acyclic u₁ u₂ v₁ v₂) =
      Units.map (IsLocalRing.residue k).toMonoidHom
        (-(u₁ * u₂) / (v₁ * v₂)) := sorry

end CategoryTheory.TwoPeriodicEndomorphism.FourByFour
