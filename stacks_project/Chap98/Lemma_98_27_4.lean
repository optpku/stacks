/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_27_4_Functor
public import stacks_project.Chap98.Lemma_98_27_4_Triple
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 98.27.4: in Situation 98.27.1 the rule F sending a locally Noetherian
scheme V over S to the set of compatible triples (Z, u', hatx), and sending a
morphism φ : V2 ⟶ V1 of locally Noetherian schemes over S to the map given by
inverse image of the closed subset, restriction of the open morphism, and
completion of φ, is a contravariant functor. -/
@[stacks 0GHA]
#check ContractionSituation.functor
