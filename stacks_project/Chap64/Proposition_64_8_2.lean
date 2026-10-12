/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Proposition_64_8_2_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.GradedPiece

/- Proposition 64.8.2. In the situation of the filtered derived functor RT of a
left exact functor T : 𝒜 ⥤ₗ ℬ with enough injectives on 𝒜, the p-th associated-graded
functor commutes with RT: gr^p ∘ RT_filtered ≅ RT_ordinary ∘ gr^p as functors
DF⁺(𝒜) ⥤ D⁺(ℬ). -/
@[stacks 03TE] #check @iso

/- Uniqueness comparison used to construct `iso`. -/
#check @CategoryTheory.FilteredObject.FiniteDerived.Plus.GradedPiece.RightDerived.canonicalIso
