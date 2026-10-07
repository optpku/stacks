module

public import stacks_project.Chap97.Proposition_97_10_4_Space
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

/- Proposition 97.10.4: Let `S` be a scheme. Let `Z ⟶ B` and `X ⟶ B` be morphisms
of algebraic spaces over `S`. If `Z ⟶ B` is finite locally free then
`Mor_B(Z, X)` is an algebraic space. -/
@[stacks 05Y7]
#check (instIsAlgebraicSpace :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B} [FiniteLocallyFree Z.hom],
      IsAlgebraicSpace (smallFunctor Z X))
