/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence
import StacksCheckRecall

/-!
# Derived tensor spectral sequences

This chapter file recalls the canonical derived-tensor spectral-sequence API from `ReasLib`.

@stack 0662
-/

@[expose] public section

/- Example 15.62.4 (1), tag `0662`: the right-cohomology spectral sequence has page two
`H^p(K ⊗[R]^L H^q(L))` and converges to derived tensor cohomology. -/
@[stacks 0662 "(1) right-cohomology spectral sequence"]
#check @CategoryTheory.DerivedCategory.TensorSpectralSequence.existsRightCohomology

/- Example 15.62.4 (2), tag `0662`: the left-cohomology spectral sequence has page two
`H^p(H^q(K) ⊗[R]^L L)` and has the same abutment. -/
@[stacks 0662 "(2) left-cohomology spectral sequence"]
#check @CategoryTheory.DerivedCategory.TensorSpectralSequence.existsLeftCohomology

/- Example 15.62.4 (3), tag `0662`: cohomological page-two differentials have bidegree
`(2, -1)`. -/
@[stacks 0662 "(3) page-two differential"]
#check @CategoryTheory.DerivedCategory.TensorSpectralSequence.pageTwoDifferential

/- The paired existence statement and reusable source predicates. -/
#check @CategoryTheory.DerivedCategory.TensorSpectralSequence.existsPair
#check @CategoryTheory.DerivedCategory.TensorSpectralSequence.IsRightCohomology
#check @CategoryTheory.DerivedCategory.TensorSpectralSequence.IsLeftCohomology
