/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Properties
import StacksCheckRecall

/-!
# Lemma 25.12.2 infrastructure compatibility

The reusable basis-covering, single-arrow extension, and degreewise basis-membership APIs are
owned by `ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.{Basis,Adjoin}` and
`ReasLib.CategoryTheory.Sites.Hypercovering.Properties`. This module retains the historical
Chapter 25 import path.
-/

/- The single-arrow extension used in the induction is the reusable formal-coproduct
construction. -/
#check @CategoryTheory.Limits.FormalCoproduct.addSingleton

/- Its source-membership condition separates into the old family and the adjoined source. -/
#check @CategoryTheory.Limits.FormalCoproduct.addSingleton_objectsIn_iff

/- A basis covering remains a basis covering after this extension once the enlarged family is
covering and the new source lies in the basis. -/
@[stacks 0DAV "basis covering after adjoining one arrow"]
#check @CategoryTheory.Limits.FormalCoproduct.IsBasisCovering.addSingleton

/- The resulting fixed-target hypercovering condition is recorded degreewise. -/
@[stacks 0DAV "degreewise basis membership"]
#check @CategoryTheory.Hypercovering.degreewiseObjectsIn
