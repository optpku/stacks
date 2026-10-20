module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.KFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {R : Type u} [CommRing R]
variable (A B C : CochainDGAlgebra.{u, u} R)
variable (hC : C.IsKFlat)
variable (N : DifferentialGradedBimodule A B)
variable (N' : DifferentialGradedBimodule B C)

/- Lemma 22.34.3 (1) (09S4): if `C` is K-flat over `R`, the canonical map
`(A ⊗[R] B)_B ⊗_Bᴸ {}_B(B ⊗[R] C)_C ⟶ A ⊗[R] (B ⊗[R] C)` is invertible. -/
@[stacks 09S4] #check
  (DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.comparison_isIso_of_isKFlat
      A B C hC :
    IsIso (DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.comparison A B C))

/- Lemma 22.34.3 (2) (09S4): under the same K-flatness hypothesis, the conclusion of
Lemma 22.34.2 holds for every pair of composable differential graded bimodules. -/
@[stacks 09S4] #check
  (DifferentialGradedBimodule.Tensor.Derived.existsComposite_of_isKFlat N N' hC :
    ∃ N'' : DifferentialGradedBimodule A C,
      DifferentialGradedBimodule.Tensor.Derived.RepresentsComposite N N' N'')

#check @DifferentialGradedBimodule.Tensor.algebra
#check @DifferentialGradedBimodule.Tensor.AlgebraTensor.tripleRightModule
#check @DifferentialGradedBimodule.Tensor.AlgebraTensor.tripleRightModule_toCochainComplex
#check @DifferentialGradedBimodule.Tensor.AlgebraTensor.bimoduleContraction
#check @DifferentialGradedBimodule.Tensor.AlgebraTensor.contraction
#check @DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.comparison
#check @DifferentialGradedBimodule.Tensor.Derived.RepresentsComposite
#check @DifferentialGradedBimodule.Tensor.Derived.comparison
#check @DifferentialGradedBimodule.Tensor.Derived.comparison_isIso_of_computesAt
