/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Remark_90_22_3_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Remark 90.22.3 (1): if `(U, R, s, t, c)` is a groupoid in functors on
`ArtinianLocalAlgCat Λ k`, there is a canonical isomorphism
`restrictInclusion (completion G) ≅ G`. -/
@[stacks 06KF] #check GroupoidInFunctors.restrictInclusionCompletionIso

/- Remark 90.22.3 (2): if `(U, R, s, t, c)` is a groupoid in functors on
`CompleteLocalAlgCat Λ k` whose object and arrow functors preserve limits, for
example if they are representable, there is a canonical isomorphism
`completion (restrictInclusion G) ≅ G`. -/
@[stacks 06KF] #check GroupoidInFunctors.completionRestrictInclusionIso
