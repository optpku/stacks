/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford
public import stacks_project.Chap94.Definition_94_12_2_Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- Definition 94.12.2: an algebraic stack `X` over a scheme `S` contained in
`(Sch/S)_fppf` is a Deligne-Mumford stack if there exists a scheme `U` over `S`
and a surjective étale 1-morphism `slice U ⟶ X`. -/
@[stacks 03YO] #check AlgebraicGeometry.DeligneMumfordStack
