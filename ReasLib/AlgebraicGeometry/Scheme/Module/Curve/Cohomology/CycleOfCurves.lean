/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Curve.CycleOfCurves
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Over an algebraically closed field `k`, a projective one-dimensional
`k`-scheme containing a cycle of curves has nonzero first cohomology of its
structure sheaf. -/
theorem firstCohomology_structureSheaf_not_isZero_of_cycleOfCurves
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Projective X.hom]
    (hXdim : topologicalKrullDim X.left = 1) {n : ℕ}
    (C : Fin n → X.left.IdealSheafData) (x : Fin n → X.left)
    (hΓ : Scheme.IsCycleOfCurves C x) :
    ¬ IsZero (Scheme.Hom.cohomology X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1) := sorry

end AlgebraicGeometry.SchemeOverField
