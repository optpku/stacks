module

public import stacks_project.Chap91.Situation_91_6_2_Diagram
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

universe u

/- Situation 91.6.2: a morphism `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` of ringed spaces
together with a commutative diagram of first-order thickenings whose top row is
a short exact sequence of first-order thickenings of `X`, whose bottom row is a
short exact sequence of first-order thickenings of `S`, each `f'_i` restricts
to `f`, each pair `(f, f'_i)` is a strict morphism of thickenings, and each
`f'_i` is flat, together with an `𝒪'_2`-module `F'_2` flat over `S'_2` with
`F = F'_2|_X` and the canonical splitting `π : X'_1 ⟶ X` from Remark 91.4.9. -/
@[stacks 08VS] #check @SesFlatThickenings

#check @SesFlatThickenings.canonicalSplitting
#check @SesFlatThickenings.moduleRestrict
#check @SesFlatThickenings.of
