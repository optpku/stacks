/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ResidueGalois
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- The geometric point of the rational spectrum induced by the canonical inclusion into
the complex numbers is not algebraic. -/
theorem complex_not_isAlgebraic :
    ¬ (AlgebraicGeometry.Scheme.GeometricPoint.of ℂ
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))).IsAlgebraic := sorry

end AlgebraicGeometry.Scheme.GeometricPoint
