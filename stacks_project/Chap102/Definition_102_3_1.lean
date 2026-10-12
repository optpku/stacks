/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap102.Definition_102_3_1_LimitPreserving
import StacksCheckRecall

@[expose] public section

/- Definition 102.3.1: a 1-morphism f : 𝒳 ⟶ 𝒴 of categories fibred in groupoids
over (Sch/S)_fppf is limit preserving if for every directed inverse limit
U = lim U_i of affine schemes over S, the square of fibre categories
colim 𝒳_{U_i} ⟶ 𝒳_U over colim 𝒴_{U_i} ⟶ 𝒴_U is 2-cartesian. -/
@[stacks 0CMR] #check AlgebraicGeometry.Groupoids.Hom.LimitPreserving
