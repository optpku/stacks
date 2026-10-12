/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Example_67_53_3_Homeomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineSpace
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- Example 67.53.3 (1): the first arrow `𝔸¹_k ⟶ X` is étale surjective. -/
@[stacks 05Z6] #check etale_atlas
@[stacks 05Z6] #check locallySurjective_atlas

/- Example 67.53.3 (2): the second arrow `X ⟶ 𝔸¹_k` is universally injective. -/
@[stacks 05Z6] #check universallyInjective_toAffineLine

/- Example 67.53.3 (3): the composition is the map `x ↦ x²`. -/
@[stacks 05Z6] #check toAffineLine_comp_atlas

/- Example 67.53.3 (4): the composition is universally closed. -/
@[stacks 05Z6] #check squareMap_universallyClosed
@[stacks 05Z6] #check universallyClosed_comp_atlas_toAffineLine

/- Example 67.53.3 (5): the map `X ⟶ 𝔸¹_k` is a universal homeomorphism. -/
@[stacks 05Z6] #check universalHomeomorphism_toAffineLine

/- Example 67.53.3 (6): the map `X ⟶ 𝔸¹_k` is not separated. -/
@[stacks 05Z6] #check not_separated_toAffineLine
