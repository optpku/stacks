/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_6_1_Cover
import StacksCheckRecall

@[expose] public section

/- Lemma 66.6.1: let `S` be a scheme and `X` an algebraic space over `S`. There exists a
surjective étale morphism `U ⟶ X` where `U` is a disjoint union of affine schemes. We may
in addition assume each of these affines maps into an affine open of `S`. -/
@[stacks 03FX] #check AlgebraicGeometry.AlgebraicSpace.exists_affineEtaleCover
