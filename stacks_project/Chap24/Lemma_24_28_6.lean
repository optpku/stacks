import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Localization
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.28.6: let `𝒜` and `ℬ` be differential graded algebras and let
`𝒩` be a differential graded `(𝒜, ℬ)`-bimodule which is good as a
left `𝒜`-module.  For the fixed-right-factor tensor functor, the neutral hypothesis is
that the functor inverts the chosen denominator property in its left variable.  The canonical
pointwise consequence is `HasPointwiseLeftDerivedFunctor`; the localization comparison then gives
the usual left-derived computation criterion at an object.

The algebraic DG owner packages the exact tensor specialization: left property P implies that
ordinary tensoring inverts quasi-isomorphisms, every object computes the derived value, and the
derived-to-underived comparison is an isomorphism.  The sheaf-DG analogue remains a model
boundary.
-/
@[stacks 0FTK "left-good bimodules compute derived tensor products"]
#check @DifferentialGradedBimodule.Tensor.derivedCounit_isIso_of_hasLeftPropertyP
#check @DifferentialGradedBimodule.Tensor.computesAt_of_hasLeftPropertyP
#check @DifferentialGradedBimodule.Tensor.derivedCounit_app_isIso_of_hasLeftPropertyP
#check @DifferentialGradedBimodule.Tensor.derivedSourceFunctor_isInvertedBy_of_hasLeftPropertyP
