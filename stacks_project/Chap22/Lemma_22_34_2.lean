/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.AlgebraTensor
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable {A B C : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (N' : DifferentialGradedBimodule B C)
variable (h_comparison : IsIso
  (DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.comparison A B C))

/- Lemma 22.34.2 (0BZ5): invertibility of the algebra-tensor comparison implies that every
composite of derived tensor functors is represented by a differential graded bimodule. -/
@[stacks 0BZ5] #check
  (DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.existsComposite_of_comparison
      N N' h_comparison :
    ∃ N'' : DifferentialGradedBimodule A C,
      DifferentialGradedBimodule.Tensor.Derived.RepresentsComposite N N' N'')

#check @DifferentialGradedBimodule.Tensor.Derived.AlgebraTensor.comparison
#check @DifferentialGradedBimodule.Tensor.Derived.RepresentsComposite
