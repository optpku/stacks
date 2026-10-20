/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Triangulated.Generators

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- The perfect derived category of a proper smooth scheme over a field admits a strong
triangulated generator. -/
theorem existsStrongTriangulatedGenerator
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Smooth X.hom] :
    ∃ E : PerfectDerived X,
      (CategoryTheory.ObjectProperty.singleton E).IsStrongTriangulatedGenerator := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived
