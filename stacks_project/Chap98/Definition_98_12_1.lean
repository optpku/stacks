/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap107.Definition_107_4_1_VersalRing
import StacksCheckRecall

@[expose] public section

/- Definition 98.12.1
Let S be a locally Noetherian scheme. Let p : 𝒳 ⟶ (Sch/S)_fppf be a category
fibred in groupoids. Let ξ = (R, ξ_n, f_n) be a formal object. Set
k = ResidueField ξ.base.carrier and x0 = ξ.stageOne. We say ξ is versal if ξ
as a formal object of F_{𝒳, k, x0} (Remark 98.9.2) is versal in the sense of
Formal Deformation Theory, Definition 90.8.9. This is owned by
AlgebraicGeometry.GroupoidsOver.FormalObject.IsVersal. -/
@[stacks 0CXJ] #check AlgebraicGeometry.GroupoidsOver.FormalObject.IsVersal

#check AlgebraicGeometry.GroupoidsOver.FormalObject.IsVersal.spec
