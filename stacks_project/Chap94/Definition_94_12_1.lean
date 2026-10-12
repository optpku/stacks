/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- Definition 94.12.1: an algebraic stack over a scheme `S` contained in
`(Sch/S)_fppf` is a category `p : X ⟶ (Sch/S)_fppf` over `(Sch/S)_fppf` that is
a stack in groupoids, whose diagonal `Δ : X ⟶ X × X` is representable by
algebraic spaces, and that admits a scheme `U` over `S` with a surjective smooth
1-morphism `slice U ⟶ X`. -/
@[stacks 026O] #check AlgebraicGeometry.AlgebraicStack
