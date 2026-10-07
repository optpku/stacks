module

public import stacks_project.Chap59.Lemma_59_65_2_Equivalence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.65.2: finite-type locally constant sheaves of `Λ`-modules on the small
étale site of an irreducible geometrically unibranch scheme `X` are equivalent to
finite `Λ`-modules with a continuous `π₁(X, x̄)`-action, for an arbitrary ring `Λ`. -/
@[stacks 0GIY]
#check finiteTypeLocallyConstantModule_equivalence_finitePi1Modules
