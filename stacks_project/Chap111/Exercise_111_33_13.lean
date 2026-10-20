module

public import ReasLib.AlgebraicGeometry.PuncturedAffineLine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.PuncturedAffineLine

/- Exercise 111.33.13 (1): the source of `hom` is an integral scheme. -/
@[stacks 028Z] #check
  (AlgebraicGeometry.PuncturedAffineLine.instIsIntegralPuncturedAffineLine :
    IsIntegral AlgebraicGeometry.PuncturedAffineLine.puncturedAffineLine)

/- Exercise 111.33.13 (2): the target of `hom` is an integral scheme. -/
@[stacks 028Z] #check
  (AlgebraicGeometry.PuncturedAffineLine.instIsIntegralAffineLine :
    IsIntegral AlgebraicGeometry.PuncturedAffineLine.affineLine)

/- Exercise 111.33.13 (3): the induced stalk maps
`𝒪_{affineLine, hom x} ⟶ 𝒪_{puncturedAffineLine, x}` are surjective. -/
@[stacks 028Z] #check
  (AlgebraicGeometry.PuncturedAffineLine.stalkMap_surjective :
    ∀ x : AlgebraicGeometry.PuncturedAffineLine.puncturedAffineLine,
      Function.Surjective (AlgebraicGeometry.PuncturedAffineLine.hom.stalkMap x))

/- Exercise 111.33.13 (4): `hom` is not a closed immersion. -/
@[stacks 028Z] #check
  (AlgebraicGeometry.PuncturedAffineLine.not_isClosedImmersion :
    ¬ IsClosedImmersion AlgebraicGeometry.PuncturedAffineLine.hom)
