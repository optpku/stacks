/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.GroundTensor
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedBimodule

universe u

variable (R : Type u) [CommRing R]
variable {A B C : CochainDGAlgebra.{u, u} R}
variable (N : DifferentialGradedBimodule.{u, u, u, u} A B)
variable (N' : DifferentialGradedBimodule.{u, u, u, u} B C)
variable (hAC : Tensor.Derived.GroundTensor.RepresentsDerived A C)

/- Lemma 22.38.2 (0BZ8): if `A ⊗[R] C` represents `A ⊗[R]ᴸ C`, then for any
composable differential graded bimodules `N` and `N'`, their composite derived tensor functor
is represented by some differential graded `(A, C)`-bimodule. -/
@[stacks 0BZ8] #check
  (Tensor.Derived.existsComposite N N' hAC :
    ∃ N'' : DifferentialGradedBimodule.{u, u, u, u} A C,
      Tensor.Derived.RepresentsComposite N N' N'')

#synth DerivedCategory.DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} R)

#check @Tensor.Derived.GroundTensor.comparison
#check @Tensor.Derived.GroundTensor.RepresentsDerived
#check @Tensor.Derived.RepresentsComposite
#check @Tensor.bimodule
#check @Tensor.Derived.compositeCounit
#check @Tensor.Derived.comparison
#check @Tensor.Derived.comparison_isIso_of_computesAt
