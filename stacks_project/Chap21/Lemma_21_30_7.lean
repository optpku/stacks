/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Vanishing
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.7

The induction step for local comparison vanishing is owned by `ReasLib`; this file is a
source-facing recall facade.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology.TopologyComparison

/- Lemma 21.30.7 (0EZE): `(V_n) ⇒ (V_(n + 1))`. -/
@[stacks 0EZE]
#check @Vanishing.localVanishing_succ

end
