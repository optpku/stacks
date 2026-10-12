/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
import StacksCheckRecall

@[expose] public section

/- Definition 98.11.1: a category 𝒳 fibred in groupoids over (Sch/S)_fppf is
limit preserving if for every affine scheme T over S which is a directed inverse
limit T = lim T_i of affine schemes T_i over S, the comparison
colim 𝒳_{T_i} ⟶ 𝒳_T of fibre categories is an equivalence. -/
@[stacks 07XL] #check AlgebraicGeometry.Groupoids.LimitPreserving
