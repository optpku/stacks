/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Remark_90_7_10_Adjunction
public import stacks_project.Chap90.Remark_90_7_10_Functors
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Remark 90.7.10 (1): CofSet(C) is the 1-category of cofibered sets over C, identified
with the functor category C ⥤ Type via ofTypeValuedFunctor. -/
@[stacks 06HB] #check Functor.ofTypeValuedFunctor

/- Remark 90.7.10 (2): completion and restriction restrict to 1-functors
CofSet(C_Λ) ⇄ CofSet(Ĉ_Λ) and are adjoints via
typesRestrictInclusion ⊣ typesCompletionFunctor. -/
@[stacks 06HB] #check Functor.typesCompletionAdjunction

/- Remark 90.7.10 (3): the counit hat F |_{C_Λ} ⟶ F is an isomorphism. -/
@[stacks 06HB] #check Functor.typesCompletionCounitIso
