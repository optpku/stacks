/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Terminal
import StacksCheckRecall

@[expose] public section

/- Lemma 21.43.5 (0H0S): after passing to the slice over `U`, derived sections induce a
bijection on Hom sets from a canonical quasi-coherent object to an arbitrary derived module. -/
@[stacks 0H0S]
#check @CategoryTheory.ModulesOnCategory.Chaotic.Terminal.homMap_bijective

#check @CategoryTheory.ModulesOnCategory.Chaotic.Terminal.homMap
