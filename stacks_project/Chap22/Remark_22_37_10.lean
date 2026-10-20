/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Hochschild
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (e : DifferentialGradedBimodule.Derived.Category A A ≌
  DifferentialGradedBimodule.Derived.Category B B)
variable [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
variable (hΔ : e.functor.obj (DifferentialGradedBimodule.Derived.diagonalObject A) ≅
  DifferentialGradedBimodule.Derived.diagonalObject B)
variable (n : ℤ)

/- Remark 22.37.10 (09ST): an additive `R`-linear, shift-compatible equivalence between the derived
categories of `(A, A)`- and `(B, B)`-bimodules which identifies their diagonal objects induces
an `R`-linear equivalence `HHⁿ(A) ≃ₗ[R] HHⁿ(B)`. -/
@[stacks 09ST] #check
  (CochainDGAlgebra.Hochschild.linearEquiv e hΔ n :
    CochainDGAlgebra.Hochschild.Cohomology A n ≃ₗ[R]
      CochainDGAlgebra.Hochschild.Cohomology B n)
