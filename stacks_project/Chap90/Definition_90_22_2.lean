/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_22_2_Completion
public import stacks_project.Chap90.Definition_90_22_2_TypesCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 90.22.2: Let `(U, R, s, t, c)` be a groupoid in functors on
`ArtinianLocalAlgCat Λ k`. The completion of `(U, R, s, t, c)` is the groupoid in
functors `GroupoidInFunctors.completion G` on `CompleteLocalAlgCat Λ k`, obtained by
completing the object and arrow functors and the source, target, identity, and inverse
maps, and transporting composition along `Functor.typesCompletionPullbackIso`. -/
@[stacks 06KE]
#check GroupoidInFunctors.completion
