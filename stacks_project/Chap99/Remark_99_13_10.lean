/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap99.Lemma_99_13_9
public import stacks_project.Chap98.Lemma_98_24_4
public import stacks_project.Chap98.Lemma_98_22_2

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
open AlgebraicGeometry.GroupoidsOver

/- Remark 99.13.10 (1): Lemma 99.13.9, that `Spaces'_{fp, flat, proper}` satisfies
openness of versality over `specZ` and, after Remark 99.13.5, over any
Noetherian base `S`, can also be shown by the two Artin routes below. In both
cases one uses the deformation and obstruction theory of Cotangent Section
92.23 to translate the needed properties into Ext-groups to which Lemma
75.23.3 applies. The obstruction-theory route, using the full cotangent
complex, is the standard method. -/
@[stacks 0D1P] #check opennessOfVersality

/- Remark 99.13.10 (2): the first alternative is Artin's Axioms Lemma 98.24.4
(dual obstruction), as in the first proof of Lemma 99.5.11. -/
@[stacks 0D1P] #check DualObstruction.exists_isVersalAt_nhd_of_closed

/- Remark 99.13.10 (3): the second, standard alternative is an obstruction
theory as in Artin's Axioms Lemma 98.22.2, as in the second proof of Lemma
99.5.11. -/
@[stacks 0D1P] #check OpennessOfVersality.ofObstructionTheory
