/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

-- Pullback of lifted sheafified representables belongs to the generic ReasLib API.
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 7.13.5 (04D3): sheaf pullback along a continuous functor sends a lifted sheafified
representable to the lifted sheafified representable of its image. -/
@[stacks 04D3] #check @CategoryTheory.Functor.SheafifiedRepresentable.pullbackIso

#check @CategoryTheory.Functor.SheafifiedRepresentable.pullbackComparison
