module

public import stacks_project.Chap111.Exercise_111_33_13_PuncturedAffineLine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.PuncturedAffineLine

/- Exercise 111.33.13 (1): the source of `hom` is an integral scheme. -/
@[stacks 028Z] #check instIsIntegralPuncturedAffineLine

/- Exercise 111.33.13 (2): the target of `hom` is an integral scheme. -/
@[stacks 028Z] #check instIsIntegralAffineLine

/- Exercise 111.33.13 (3): the induced stalk maps
`𝒪_{affineLine, hom x} ⟶ 𝒪_{puncturedAffineLine, x}` are surjective. -/
@[stacks 028Z] #check stalkMap_surjective

/- Exercise 111.33.13 (4): `hom` is not a closed immersion. -/
@[stacks 028Z] #check not_isClosedImmersion
