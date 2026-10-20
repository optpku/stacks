/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular

/-!
# External Tensor Bimodules of Differential Graded Algebras

The tensor DGA `A.opposite ⊗[R] B`, acting on itself, is the canonical differential graded
`(A, B)`-bimodule with underlying complex `A ⊗[R] B`.  This file owns that construction
independently of any derived-composition application.
-/

@[expose] public section

noncomputable section

universe u v

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]

/-- The external tensor `A ⊗[R] B` as its canonical differential graded `(A, B)`-bimodule. -/
@[stacks 0BZ4 "external tensor differential graded bimodule"]
noncomputable abbrev algebra (A B : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedBimodule.{u, v, v, v} A B :=
  (CochainDGAlgebra.enveloping A B).regularModule

/-- The right `B`-module underlying the external tensor bimodule `A ⊗[R] B`. -/
@[stacks 0BZ4 "right module of the external tensor bimodule"]
noncomputable abbrev algebraRight (A B : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v} B :=
  (algebra A B).toRightModule

/-- The left `A`-module underlying the external tensor bimodule `A ⊗[R] B`. -/
@[stacks 0BZ4 "left module of the external tensor bimodule"]
noncomputable abbrev algebraLeft (A B : CochainDGAlgebra.{u, v} R) :
    LeftDifferentialGradedModule.{u, v} A :=
  (algebra A B).toLeftModule

/-- The external tensor bimodule has the total tensor complex as its underlying complex. -/
@[simp, stacks 0BZ4 "underlying complex of the external tensor bimodule"]
theorem algebra_toCochainComplex (A B : CochainDGAlgebra.{u, v} R) :
    (algebra A B).toCochainComplex =
      CochainDGAlgebra.Tensor.complex A.opposite B := sorry

/-- Restriction to the right factor preserves the total tensor complex. -/
@[simp, stacks 0BZ4 "underlying complex of the right external tensor module"]
theorem algebraRight_toCochainComplex (A B : CochainDGAlgebra.{u, v} R) :
    (algebraRight A B).toCochainComplex =
      CochainDGAlgebra.Tensor.complex A.opposite B := sorry

/-- Restriction to the left factor preserves the total tensor complex. -/
@[simp, stacks 0BZ4 "underlying complex of the left external tensor module"]
theorem algebraLeft_toCochainComplex (A B : CochainDGAlgebra.{u, v} R) :
    (algebraLeft A B).toCochainComplex =
      CochainDGAlgebra.Tensor.complex A.opposite B := sorry

end DifferentialGradedBimodule.Tensor
