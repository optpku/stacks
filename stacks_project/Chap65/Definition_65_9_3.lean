/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 65.9.3: a presentation of an algebraic space `F` over `S` is given by a scheme
`U` over `S`, an étale equivalence relation `R` on `U` over `S`, and a surjective étale morphism
`U ⟶ F` such that `R = U ×_F U`. -/
@[stacks 0263] #check (AlgebraicGeometry.AlgebraicSpace.Presentation :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
