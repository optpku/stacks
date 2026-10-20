/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.ChangeOfRings
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Derived

/-!
# The Diagonal Differential Graded Bimodule

A differential graded algebra is canonically a bimodule over itself.  We define this object by
specializing the extension-of-scalars bimodule to the identity DGA homomorphism, so its signs and
enveloping-algebra action are inherited from the shared change-of-rings construction.
-/

@[expose] public section

noncomputable section

universe u v

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]

/-- The diagonal differential graded `(A, A)`-bimodule: `A` with its regular left and right
actions. -/
@[stacks 09ST "diagonal differential graded bimodule"]
def diagonal (A : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedBimodule.{u, v, v, v} A A :=
  ChangeOfRings.extension (CochainDGAlgebra.Hom.id A)

/-- The right module underlying the diagonal bimodule is the regular right module. -/
@[simp]
theorem diagonal_toRightModule (A : CochainDGAlgebra.{u, v} R) :
    (diagonal A).toRightModule = A.regularModule := sorry

/-- The complex underlying the diagonal bimodule is the complex underlying the DGA. -/
@[simp]
theorem diagonal_toCochainComplex (A : CochainDGAlgebra.{u, v} R) :
    (diagonal A).toCochainComplex = A.toCochainComplex := sorry

/-- The left action of the diagonal bimodule is multiplication in the DGA. -/
@[simp]
theorem diagonal_leftMul (A : CochainDGAlgebra.{u, v} R) (i p : ℤ)
    (a : A.X i) (b : A.X p) :
    (diagonal A).leftMul i p a b = A.mul i p a b := sorry

namespace Derived

/-- The diagonal bimodule as an object of the derived category of `(A, A)`-bimodules. -/
@[stacks 09ST "derived diagonal bimodule"]
abbrev diagonalObject (A : CochainDGAlgebra.{u, v} R) : Category A A :=
  object (diagonal A)

end Derived

end DifferentialGradedBimodule
