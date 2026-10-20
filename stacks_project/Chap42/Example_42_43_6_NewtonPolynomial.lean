/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton

/- The chapter compatibility module exposes the canonical Newton polynomial owner. -/
#check (AlgebraicGeometry.ChernPolynomial.Newton.polynomial :
  ℕ+ → MvPolynomial ℕ ℤ)
