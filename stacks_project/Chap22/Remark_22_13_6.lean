module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InternalHom.Evaluation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace DifferentialGradedModule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (M : DifferentialGradedModule A)
variable (N : CochainComplex (ModuleCat.{v} R) ℤ)

/- Remark 22.13.6 (0FQ8): Koszul-signed evaluation transposes to the canonical right-DG-module
map from `M` into its double internal Hom. -/
@[stacks 0FQ8] #check
  (OfRight.evaluation M N : M ⟶ OfLeft.obj (OfRight.obj M N) N)

#check @OfRight.evaluationPairing
#check @OfRight.evaluationPairing_tmul
#check @OfRight.evaluation_transpose
#check @OfRight.evaluation_apply

end DifferentialGradedModule.InternalHom
