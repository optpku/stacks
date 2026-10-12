/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.BaseChange

/-!
# Lemma 16.2.7 compatibility façade

The presentation-level and existential base-change APIs are neutral algebra
infrastructure.  They are owned by `ReasLib.RingTheory.Smooth.Standard` rather
than this textbook chapter, while this file preserves the source import path.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

/- Lemma 16.2.7: base change preserves elementary and strictly standard
elements, with the presentation-level transport lemmas available for reuse. -/
#check Presentation.BaseChange.ker
#check Presentation.BaseChange.algebraMap_map
#check Presentation.RelationIdeal.baseChange
#check Presentation.RelationCondition.baseChange
#check Presentation.JacobianMinor.baseChange
#check Presentation.JacobianIdeal.baseChange
#check Presentation.IsElementaryFor.baseChange
#check Presentation.IsStrictlyFor.baseChange
#check Presentation.IsElementaryStandard.baseChange
#check Presentation.IsStrictlyStandard.baseChange
@[stacks 07CC "elementary standard elements under base change"]
#check IsElementaryStandard.baseChange

@[stacks 07CC "strictly standard elements under base change"]
#check IsStrictlyStandard.baseChange

end Algebra
