module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Shift
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedBimodule
open scoped DifferentialGradedModule

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable (N : DifferentialGradedBimodule.{u, w, x, y} A B)
variable (M : DifferentialGradedModule.{u, v} A) (k : ℤ)

/- Remark 22.29.2 (0FQN): the sign-free comparison identifies the shift of
`M ⊗_A N` with `M[k] ⊗_A N`. -/
@[stacks 0FQN] #check
  (Tensor.shiftIso N M k : (Tensor.obj M N)[k] ≅ Tensor.obj (M[k]) N)
