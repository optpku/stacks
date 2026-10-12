/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap99.Lemma_99_14_13
public import stacks_project.Chap98.Lemma_98_22_2
public import stacks_project.Chap99.Lemma_99_14_6
public import stacks_project.Chap99.Lemma_99_13_9

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Polarized
open AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
open AlgebraicGeometry.GroupoidsOver

/- Remark 99.14.14 (1): Lemma 99.14.13, that Polarized satisfies openness of
versality over `specZ` and, after Remark 99.14.5, over any Noetherian base `S`,
can also be shown by the two routes below. The `specZ` specialization is
`instOpennessOfVersality`. -/
@[stacks 0D4W] #check instOpennessOfVersality_over

/- Remark 99.14.14 (2): the first alternative is an obstruction theory as in
Artin's Axioms Lemma 98.22.2, as in the second proof of Lemma 99.5.11. To do
this one has to generalize the deformation and obstruction theory of Cotangent
Section 92.23 from ringed topoi to pairs of algebraic spaces and quasi-coherent
modules. -/
@[stacks 0D4W] #check OpennessOfVersality.ofObstructionTheory

/- Remark 99.14.14 (3): the second alternative uses that the forgetful
1-morphism `toFpFlatProper : Polarized ⟶ Spaces'_{fp, flat, proper}` is
algebraic (Lemma 99.14.6). -/
@[stacks 0D4W] #check instAlgebraicStack_twoFibreProduct

/- Remark 99.14.14 (4): openness of versality of the target
`Spaces'_{fp, flat, proper}` is already known by Lemma 99.13.9 and
Remark 99.13.10. -/
@[stacks 0D4W] #check opennessOfVersality
