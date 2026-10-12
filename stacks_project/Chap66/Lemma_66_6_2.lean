/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_6_2_Cover
import StacksCheckRecall

@[expose] public section

/- Lemma 66.6.2: let `S` be a scheme and `X` an algebraic space over `S`. There exists a
Zariski covering `X = ⋃ X_i` such that each algebraic space `X_i` has a surjective étale
covering by an affine scheme. We may in addition assume each `X_i` maps into an affine
open of `S`. -/
@[stacks 03FY] #check AlgebraicGeometry.AlgebraicSpace.exists_affineEtaleZariskiCover
