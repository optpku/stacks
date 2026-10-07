module

public import stacks_project.Chap42.Lemma_42_61_2_Comparison
import StacksCheckRecall

/- Lemma 42.61.2: for a field `k`, a scheme `X` locally of finite type over `k`, and
`p : ℤ`, degree-`p` bivariant classes for `X ⟶ Spec k` are canonically identified with
`CH_{-p}(X)`. -/
@[stacks 0FBW] #check @AlgebraicGeometry.BivariantClass.chowEquiv
