/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Bimodule.Hom
public import ReasLib.Algebra.Module.Graded.Bimodule.Category
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule
import StacksCheckRecall

@[expose] public section

universe u v w x

section Ordinary

variable {R A B M : Type u}
variable [CommRing R] [Ring A] [Ring B]
variable [Algebra R A] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
variable [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M]
variable [SMulCommClass A Bᵐᵒᵖ M]

/- Definition 22.28.1 (1) (0FQH): an ordinary `(A, B)`-bimodule is equivalently a module over
the ordinary enveloping algebra `A ⊗[R] Bᵐᵒᵖ`. -/
@[stacks 0FQH "ordinary bimodules"] #check
  (TensorProduct.Algebra.module : Module (TensorProduct R A Bᵐᵒᵖ) M)

end Ordinary

section Graded

variable {R A B : Type u}
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (𝒝 : ℤ → Submodule R B) [GradedAlgebra 𝒝]

/- Definition 22.28.1 (2) (0FQH): graded bimodules use the shared owner for compatible
homogeneous left and right actions. -/
@[stacks 0FQH "graded bimodules"] #check
  (GradedModule.Bimodule 𝒜 𝒝 : Type _)

#check @GradedModule.Bimodule.leftAction
#check @GradedModule.Bimodule.rightAction
#check @GradedModule.Bimodule.Hom

end Graded

section DifferentialGraded

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R)

/- Definition 22.28.1 (3) (0FQH): DG `(A, B)`-bimodules are right DG modules over the
enveloping DGA `A.opposite ⊗[R] B`. -/
@[stacks 0FQH "differential graded bimodules"] #check
  (DifferentialGradedBimodule.{u, v, w, x} A B : Type _)

#check @DifferentialGradedBimodule.toLeftModule
#check @DifferentialGradedBimodule.toRightModule
#check @DifferentialGradedBimodule.forgetToLeftModule
#check @DifferentialGradedBimodule.forgetToRightModule

end DifferentialGraded
