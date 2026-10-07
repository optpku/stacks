module

public import stacks_project.Chap76.Situation_76_56_1_Descent
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]

/- Situation 76.56.1: over a scheme `S`, a quasi-compact and quasi-separated algebraic space `X`
is equipped with a chosen affine étale surjection `φ : V ⟶ X`, a commutative factorization
`V ⟶ Y ⟶ X` with `j` an open immersion and `π` finite, and a chosen finite-type quasi-coherent
ideal `I ⊂ 𝒪_Y` whose vanishing locus is the complement of the image of `j`. -/
@[stacks 0GUY] #check (ResolutionDescent X)

end
