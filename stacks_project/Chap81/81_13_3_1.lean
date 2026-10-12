/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap81.«81_13_3_1_System»
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

/- 81.13.3.1 (1): in Situation 81.13.2 the coequalizers of the neighbourhood
coproducts form a sequential system X_1 ⟶ X_2 ⟶ X_3 ⟶ ⋯ ⟶ X. -/
@[stacks 0AGJ] #check AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.system
@[stacks 0AGJ] #check AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.toAmbient
@[stacks 0AGJ] #check AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.stageMap
@[stacks 0AGJ] #check AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.cocone

/- 81.13.3.1 (2): each morphism in the system, and each morphism to X, is a
universal homeomorphism. -/
@[stacks 0AGJ] #check AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.instUniversalHomeomorphism_stageMap
@[stacks 0AGJ] #check AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.instUniversalHomeomorphism_toAmbient
