/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Terminal
import StacksCheckRecall

@[expose] public section

/- Lemma 21.43.4 (0H0R): on a chaotic ringed site with flat restriction maps, derived sections
at a terminal object identify canonical quasi-coherent derived modules with modules over the
ring of sections at that object. -/
@[stacks 0H0R]
#check @CategoryTheory.ModulesOnCategory.Chaotic.Terminal.sections_isEquivalence

#check @CategoryTheory.ModulesOnCategory.Chaotic.Terminal.sections
