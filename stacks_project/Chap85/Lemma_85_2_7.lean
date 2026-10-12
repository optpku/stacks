/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_2_7_Morphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject

/- Lemma 85.2.7: a morphism `f : Y ⟶ X` of simplicial spaces induces a commutative
diagram of topoi `Sh(Y_n) ⟶ Sh(X_n)` over `Sh(Y_Zar) ⟶ Sh(X_Zar)`. -/
@[stacks 09W2] #check @zariskiMorphism_comp_component
