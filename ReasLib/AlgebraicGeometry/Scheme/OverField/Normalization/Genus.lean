/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.ProperBirational
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

/-- Normalization does not increase the first structure-sheaf cohomology dimension of a
proper integral curve over an algebraically closed field. These dimensions are the genera
of the normalization and the original curve. -/
theorem structureSheafH1Finrank_le
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [IsProper X.hom] :
    Scheme.Hom.cohomologyFinrank (SchemeOverField.normalization X).hom
        (SheafOfModules.unit (SchemeOverField.normalization X).left.ringCatSheaf :
          (SchemeOverField.normalization X).left.Modules) 1 ≤
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

/-- The first structure-sheaf cohomology dimension of the normalization of a proper
curve over an algebraically closed field, plus the number of any chosen distinct
singular points, is at most the first structure-sheaf cohomology dimension of the curve. -/
theorem structureSheafH1Finrank_add_n_le
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} (X : SchemeOverField k)
    [Curve X] [IsProper X.hom] (points : Fin n → X.left)
    (points_injective : Function.Injective points)
    (points_singular : ∀ index, points index ∈ Sing(X.left)) :
    Scheme.Hom.cohomologyFinrank (SchemeOverField.normalization X).hom
        (SheafOfModules.unit (SchemeOverField.normalization X).left.ringCatSheaf :
          (SchemeOverField.normalization X).left.Modules) 1 + n ≤
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

/-- The first structure-sheaf cohomology dimension of the normalization of a proper
curve over an algebraically closed field is at most that of the curve minus the number
of any chosen distinct singular points, expressed as an integer inequality. -/
theorem structureSheafH1Finrank_le_neg_n_add
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} (X : SchemeOverField k)
    [Curve X] [IsProper X.hom] (points : Fin n → X.left)
    (points_injective : Function.Injective points)
    (points_singular : ∀ index, points index ∈ Sing(X.left)) :
    (Scheme.Hom.cohomologyFinrank (SchemeOverField.normalization X).hom
        (SheafOfModules.unit (SchemeOverField.normalization X).left.ringCatSheaf :
          (SchemeOverField.normalization X).left.Modules) 1 : ℤ) ≤
      -(n : ℤ) +
        Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := by
  have normalization_bound :=
    structureSheafH1Finrank_add_n_le X points points_injective points_singular
  sorry

end AlgebraicGeometry.SchemeOverField.Normalization
