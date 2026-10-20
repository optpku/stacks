/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField.GeometricallyIntegral

variable {k : Type u} [Field k]

/-- A scheme over a field is geometrically integral exactly when it is both
geometrically reduced and geometrically irreducible. -/
theorem iff_geometricallyReduced_and_geometricallyIrreducible (X : SchemeOverField k) :
    AlgebraicGeometry.GeometricallyIntegral X.hom ↔
      AlgebraicGeometry.GeometricallyReduced X.hom ∧
        AlgebraicGeometry.GeometricallyIrreducible X.hom := sorry

end AlgebraicGeometry.SchemeOverField.GeometricallyIntegral
