/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap83.Definition_83_5_18_OrbitSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Definition 83.5.18: for `B` an algebraic space over a scheme `S` and a pre-relation
`j : R ⟶ U ⨯ U` on an algebraic space `U` over `B`, a morphism `φ : U ⟶ X` over `B` is an
orbit space for `R` if `φ` is `R`-invariant, `φ` separates `R`-orbits, and `φ` is
surjective. -/
@[stacks 0493] #check AlgebraicGeometry.AlgebraicSpace.PreRelation.IsOrbitSpace
