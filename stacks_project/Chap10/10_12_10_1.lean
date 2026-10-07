module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import StacksCheckRecall

@[expose] public section

/-!
# 10.12.10.1

@stack 00DG
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- 10.12.10.1: tensoring a right exact sequence of `R`-modules with a fixed module `N`
preserves exactness, so `M₁ ⊗[R] N ⟶ M₂ ⊗[R] N ⟶ M₃ ⊗[R] N ⟶ 0` is exact whenever
`M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is exact. This is exactly the canonical pair
`rTensor_exact` and `LinearMap.rTensor_surjective`. -/
@[stacks 00DG "right tensor exactness"]
#check @rTensor_exact
@[stacks 00DG "right tensor surjectivity"]
#check @LinearMap.rTensor_surjective
