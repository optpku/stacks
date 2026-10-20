/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.DeRham.Descent
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Descent from the universal Kähler derivation

@stack 07HY

This leaf specializes the generic descent criterion for exterior-power de Rham
families to the universal Kähler derivation.  Its image spans the module of
Kähler differentials, so consumers only supply the quotient map, its kernel
condition, and the source differential family.
-/

@[expose] public section

universe u v

namespace KaehlerDifferential.DeRham

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω]
variable [IsScalarTower A B Ω]

/-- A surjective quotient of `Ω[B⁄A]` whose kernel satisfies the degree-one
`DifferentialOperator.DeRham.KernelCondition` inherits a de Rham differential family.

The source family is explicit because the theorem uses its differential formulas rather than a
noncanonical choice of a de Rham family. -/
@[stacks 07HY]
theorem existsDescended
    (π : Ω[B⁄A] →ₗ[B] Ω) (hπ : Function.Surjective π)
    {δ : DifferentialOperator.DeRham.Family A B Ω[B⁄A]}
    (hδ : DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B) δ)
    (hcondition : DifferentialOperator.DeRham.KernelCondition π δ) :
    ∃ δΩ : DifferentialOperator.DeRham.Family A B Ω,
      DifferentialOperator.DeRham.IsDifferential
          (π.compDer (KaehlerDifferential.D A B)) δΩ ∧
        DifferentialOperator.DeRham.Descends π δ δΩ := sorry

end

end KaehlerDifferential.DeRham
