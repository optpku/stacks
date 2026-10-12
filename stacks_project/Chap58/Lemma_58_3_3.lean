/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Galois.ProfiniteCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- Lemma 58.3.3: for a topological group `G`, the automorphism group of the functor (58.3.2.1)
endowed with its profinite topology from Lemma 58.3.1 is the profinite completion of `G`. -/
@[stacks 0BMU] #check
  (CategoryTheory.DiscreteContAction.autForget_profiniteCompletionIso G :
    Aut (CategoryTheory.DiscreteContAction.forgetFinite G) ≃ₜ*
      CategoryTheory.TopologicalProfiniteCompletion.completion G)
