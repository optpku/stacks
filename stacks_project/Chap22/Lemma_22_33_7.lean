/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.FullyFaithful
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (h_compact : IsCompactObject N.rightDerivedObject)
variable (h_selfExt : N.HasSelfExtComparison)

/- Lemma 22.33.7 (09R9): compactness of the right `B`-module represented by `N`, together with
the canonical self-extension comparisons induced by the left `A`-action, makes derived
tensoring by `N` fully faithful. -/
@[stacks 09R9] #check
  (DifferentialGradedBimodule.Tensor.fullyFaithful N h_compact h_selfExt :
    (DifferentialGradedBimodule.Tensor.derivedFunctor N).FullyFaithful)

/- The concrete proof interface separates the regular-object image, compactness, and shifted
self-Hom comparison from the final compact-generator step. -/
#check @DifferentialGradedBimodule.HasSelfExtComparison
#check @DifferentialGradedBimodule.Tensor.regularObjectIso
#check @DifferentialGradedBimodule.Tensor.regularSelfExtMap
#check @DifferentialGradedBimodule.Tensor.regularSelfExtMap_bijective
#check @DifferentialGradedBimodule.Tensor.isFullyFaithfulOnSelfShifts_of_selfExt
#check @DifferentialGradedBimodule.Tensor.regularImage_isCompact
#check @DifferentialGradedBimodule.Tensor.map_bijective_of_regular
