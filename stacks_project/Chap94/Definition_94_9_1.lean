/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable (S : Scheme.{u})

/- Definition 94.9.1: a `1`-morphism `f : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf` is representable by algebraic spaces if for any `U` in `Ob((Sch/S)_fppf)`
and any `y : (Sch/U)_fppf ⟶ Y` the 2-fibre product `(Sch/U)_fppf ×_{y, Y} X` over
`(Sch/U)_fppf` is representable by an algebraic space over `U`. -/
@[stacks 02ZW]
#check (relativelyRepresentableByAlgebraicSpaces :
  MorphismProperty (GroupoidsOver S))
