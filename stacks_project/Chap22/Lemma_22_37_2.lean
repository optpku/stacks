/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.Tensor
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (hN : N.IsMoritaKernel)

/- Lemma 22.37.2 (09S7): the derived tensor functor associated to a DG bimodule is an
`R`-linear triangulated equivalence under the compactness, generation, and canonical
self-extension hypotheses. -/
@[stacks 09S7] #check
  (CochainDGAlgebra.DerivedMorita.Tensor.equivalence N hN :
    RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category A)
      (DifferentialGradedModule.Derived.Category B))

#check @CochainDGAlgebra.DerivedMorita.Tensor.isEquivalence_of_compactGenerator
#check @CochainDGAlgebra.DerivedMorita.Tensor.isEquivalence
#check @CochainDGAlgebra.DerivedMorita.Tensor.equivalence_functor
#check @CochainDGAlgebra.DerivedMorita.Tensor.equivalence_inverse
#check @DifferentialGradedBimodule.IsMoritaKernelFor.isCompact
#check @DifferentialGradedBimodule.IsMoritaKernelFor.isWeakGenerator
#check @DifferentialGradedBimodule.IsMoritaKernelFor.hasSelfExtComparison
#check @DifferentialGradedBimodule.Tensor.isFullyFaithfulOnSelfShifts_of_selfExt
#check @DifferentialGradedBimodule.TensorHom.derivedAdjunction
#check @DifferentialGradedBimodule.selfExtMap
#check @CategoryTheory.Functor.IsEquivalence.ofCompactGenerator
#check @CategoryTheory.RLinear.TriangulatedEquivalence.ofAdjunction
