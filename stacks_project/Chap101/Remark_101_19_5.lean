module

public import stacks_project.Chap101.Remark_101_19_5_AutomorphismGroup
import StacksCheckRecall

/- Remark 101.19.5
Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let `x ∈ |X|` be a point.
To indicate the equivalent conditions of Lemma 101.19.4 are satisfied for `f`
and `x` in the literature the terminology `f` is stabilizer preserving at `x`
or `f` is fixed-point reflecting at `x` is used. We prefer to say `f` induces
an isomorphism between automorphism groups at `x` and `f(x)`.
-/
@[stacks 0DTW] #check AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt
