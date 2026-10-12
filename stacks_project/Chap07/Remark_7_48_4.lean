/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Precoverage.Tautological
public import ReasLib.CategoryTheory.Sites.PrecoverageStability

@[expose] public section

universe w' w u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Remark 7.48.4 (00ZF): the formal tautological closure of a precoverage
records precisely the families tautologically equivalent to original covers.
Its isomorphism, composition, base-change, and topology APIs are reusable at
the `Precoverage` layer. -/
@[stacks 00ZF] #check @Precoverage.tautologicalClosure

/- Remark 7.48.4 (1') (00ZF): isomorphism coverings survive tautological
closure. -/
@[stacks 00ZF] #check @Precoverage.mem_tautologicalClosure_of_isIso

/- Remark 7.48.4 (2') (00ZF): indexed-composition stability survives
tautological closure. -/
@[stacks 00ZF] #check @Precoverage.comp_mem_tautologicalClosure

/- Remark 7.48.4 (3') (00ZF): chosen-base-change stability survives
tautological closure. -/
@[stacks 00ZF] #check @Precoverage.mem_tautologicalClosure_of_isPullback

/- Remark 7.48.4 (3') (00ZF): the required pullbacks along closure covers
exist whenever they exist along the original covers. -/
@[stacks 00ZF] #check @Precoverage.tautologicalClosure_hasPullbacks

/- Remark 7.48.4 (00ZF): closure leaves the associated topology unchanged. -/
@[stacks 00ZF] #check @Coverage.tautologicalClosure_toGrothendieck

/- Conversely, a precoverage satisfying the selected-cover factoring condition is promoted to the
canonical `Coverage` owner, which supplies the site-level completion of the modified axioms. -/
@[stacks 00ZF "completion of a factoring precoverage to a coverage"]
#check @Precoverage.HasFactoringPullbacks.toCoverage

@[stacks 00ZF "generated topology of the completed coverage"]
#check @Precoverage.HasFactoringPullbacks.toCoverage_toGrothendieck

end CategoryTheory
