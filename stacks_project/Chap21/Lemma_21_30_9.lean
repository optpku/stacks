module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Restriction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.9 (0EZG)

Recall facade for the topology-comparison bounded-derived restriction API.  The reusable owners are
in `TopologyComparison.Restriction`; this chapter file intentionally contains no second copy of the
derived functors or coefficient predicates.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.TopologyComparison
open CategoryTheory.GrothendieckTopology.TopologyComparison.Restriction
open CategoryTheory.ObjectProperty
open DerivedCategory
open scoped CategoryTheory.GrothendieckTopology DerivedCategory.CohomologyIn

@[stacks 0EZG]
#check @objectProperty_isWeakSerre

@[stacks 0EZG]
#check @pullback_mapsTo

@[stacks 0EZG]
#check @TopologyComparison.Restriction.pullback

@[stacks 0EZG]
#check @pushforward_mapsTo

@[stacks 0EZG]
#check @TopologyComparison.Restriction.pushforward

@[stacks 0EZG]
#check @TopologyComparison.Restriction.pushforward_isEquivalence

@[stacks 0EZG]
#check @TopologyComparison.Restriction.pullback_isEquivalence

end
