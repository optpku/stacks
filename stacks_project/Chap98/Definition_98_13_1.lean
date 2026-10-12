/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Definition_98_13_1_Versal
import StacksCheckRecall

@[expose] public section

/- Definition 98.13.1 (1)
Let S be a locally Noetherian scheme. Let X be a category fibred in groupoids
over (Sch/S)_fppf. We say X satisfies openness of versality if given a scheme
U locally of finite type over S, an object x of X over U, and a finite type
point u0 ∈ U such that x is versal at u0, there exists an open neighbourhood
u0 ∈ U' ⊂ U such that x is versal at every finite type point of U'. -/
@[stacks 07XQ]
#check AlgebraicGeometry.GroupoidsOver.OpennessOfVersality

/- Definition 98.13.1 (2)
Let f : X ⟶ Y be a 1-morphism of categories fibred in groupoids over
(Sch/S)_fppf. We say f satisfies openness of versality if given a scheme U
locally of finite type over S and an object y of Y over U, openness of
versality holds for (Sch/U)_fppf ×_Y X. -/
@[stacks 07XQ]
#check AlgebraicGeometry.Groupoids.Hom.OpennessOfVersality
