/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap45.Lemma_45_4_2_ChowMotive
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable (k : Type u) [Field k]
variable (GradedCorrespondence : Type u → Type v)
variable [Category.{w} (GradedCorrespondence k)]

/- Lemma 45.4.2: the category `Mₖ` of Chow motives is Karoubian.  Abstractly,
`ChowMotive k GradedCorrespondence` is the Karoubi envelope of a graded-correspondence
category, so it is idempotent complete. -/
@[stacks 0FGB]
#check (ChowMotive.isIdempotentComplete k GradedCorrespondence :
  IsIdempotentComplete (ChowMotive k GradedCorrespondence))
