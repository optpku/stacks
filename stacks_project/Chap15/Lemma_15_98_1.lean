module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.PseudoCoherent
import StacksCheckRecall

/-!
# Lemma 15.98.1: pseudo-coherent derived inverse limits

The reusable statement is expressed directly through `ModuleCat.DerivedTower`, its Cartesianity
predicate, and the canonical homotopy-limit API.

@stack 0CQF
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.98.1 (1), tag `0CQF`: the homotopy limit of the stated Cartesian tower is
pseudo-coherent. -/
@[stacks 0CQF "(1), pseudo-coherent inverse limit"]
#check @ModuleCat.DerivedTower.PseudoCoherent.limit

/- Lemma 15.98.1 (2), tag `0CQF`: base change of a presented homotopy limit recovers every
stage. -/
@[stacks 0CQF "(2), derived base-change comparison"]
#check @ModuleCat.DerivedTower.PseudoCoherent.Limit.baseChangeMap_isIso

/- The presentation-independent form of Lemma 15.98.1 (2). -/
#check @ModuleCat.DerivedTower.PseudoCoherent.Limit.nonemptyIso

end
