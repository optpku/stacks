/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.TsqS5p8
import StacksCheckRecall

/- Exercise 111.31.1: `extraFunction` is a regular function on `punctured`, the
complement of the point `(1, 3)` on the affine curve `t ^ 2 = s ^ 5 + 8` in
`Fin 2 → ℂ`, and is not the restriction of a regular function on `Fin 2 → ℂ`,
i.e., is not the restriction of a polynomial in `s` and `t`. -/
@[stacks 0E9D] #check
  (MvPolynomial.AffineTsqS5p8.isRegular_not_isPolynomial_extraFunction :
    MvPolynomial.IsRegular MvPolynomial.AffineTsqS5p8.extraFunction ∧
      ¬ MvPolynomial.IsPolynomial MvPolynomial.AffineTsqS5p8.extraFunction)
