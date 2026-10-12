/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_3_2
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Groupoids.Hom

/- Lemma 98.13.6 (1): if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
formally smooth on objects, then `f` satisfies (98.13.2.1). -/
@[stacks 07XW] #check IsSmoothOnPredeformations.of_formallySmoothOnObjects

/- Lemma 98.13.6 (2): if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces and smooth, then `f` satisfies (98.13.2.1). -/
@[stacks 07XW] #check IsSmoothOnPredeformations.of_smooth
