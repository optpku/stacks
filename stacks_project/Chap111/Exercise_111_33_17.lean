module

public import stacks_project.Chap111.Exercise_111_33_17_InseparableAffineLine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.InseparableAffineLine

/- Exercise 111.33.17 (1): the affine line over the purely inseparable extension
of `BaseField p` is an integral scheme. -/
@[stacks 0292] #check @instIsIntegralScheme

/- Exercise 111.33.17 (2): this scheme is 1-dimensional. -/
@[stacks 0292] #check @topologicalKrullDim_eq_one

/- Exercise 111.33.17 (3): the structure morphism to `Spec (BaseField p)` is of
finite type. -/
@[stacks 0292] #check @instFiniteTypeToBase

/- Exercise 111.33.17 (4): after the finite field extension
`ExtensionField p / BaseField p`, the fiber product is not reduced. -/
@[stacks 0292] #check @finiteFieldExtension_pullback_not_isReduced
