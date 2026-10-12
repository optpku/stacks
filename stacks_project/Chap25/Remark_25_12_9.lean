/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.CoproductSingleton
import StacksCheckRecall

/-!
# Remark 25.12.9

The fixed-target singleton-coproduct construction and its pullback and covering hypotheses are
owned by reusable ReasLib leaves.
-/

/- Remark 25.12.9: if the degreewise source coproducts of a hypercovering exist, coproducts
commute with the relevant pullbacks, and covering family morphisms induce covering arrows on
coproducts, then the degreewise singleton-coproduct replacement is again a hypercovering. -/
@[stacks 0DB2]
#check @CategoryTheory.Hypercovering.coproductSingleton

/- The topology-independent construction includes all simplicial structure maps and a natural
comparison from the original simplicial family. -/
#check @CategoryTheory.Limits.FormalCoproduct.Over.Simplicial.coproductSingleton
#check @CategoryTheory.Limits.FormalCoproduct.Over.Simplicial.toCoproductSingleton

/- The two source hypotheses have reusable categorical owners. -/
#check @CategoryTheory.Limits.FormalCoproduct.Over.CoproductSingleton.PullbackCompatible
#check @CategoryTheory.Limits.FormalCoproduct.CoproductSingleton.PreservesCovering

/- The resulting hypercovering exposes its simplicial object and comparison map. -/
#check @CategoryTheory.Hypercovering.coproductSingleton_toSimplicialObject
#check @CategoryTheory.Hypercovering.CoproductSingleton.comparison
