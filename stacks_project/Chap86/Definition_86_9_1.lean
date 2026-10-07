module

public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 86.9.1: let `S` be a scheme and let `f : X ⟶ Y` be a proper, flat morphism
of algebraic spaces over `S` which is of finite presentation. A relative dualizing complex
for `X / Y` is a pair `(ω, τ)` consisting of a `Y`-perfect object `ω` of `D(𝒪_X)` and a
map `τ : Rf_* ω ⟶ 𝒪_Y` such that for any cartesian square with `Y'` an affine scheme the
pair `(L(g')^* ω, Lg^* τ)` is isomorphic to the twisted-inverse pair
`(a'(𝒪_{Y'}), Tr_{f', 𝒪_{Y'}})`. -/
@[stacks 0E5X] #check AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
