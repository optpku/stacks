module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.TopologyChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 21.43.12 (0GZS): the K-flat sections hypothesis supplies the unit condition under
which `ε^*` and the restriction of `Rε_*` to objects whose pushforward lies in `QC O` are
mutually quasi-inverse equivalences. -/
@[stacks 0GZS]
#check @ModulesOnCategory.Chaotic.TopologyChange.pushforwardRestriction_isEquivalence_of_unitCondition

#check @ModulesOnCategory.Chaotic.TopologyChange.pullbackRestriction
#check @ModulesOnCategory.Chaotic.TopologyChange.pushforwardRestriction
#check @ModulesOnCategory.Chaotic.TopologyChange.restrictedAdjunction
#check @ModulesOnCategory.Chaotic.TopologyChange.pullbackRestriction_isEquivalence_of_unitCondition
