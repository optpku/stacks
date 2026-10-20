module

public import ReasLib.Topology.Sheaf.Subset
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe v u

/- Lemma 6.32.4: the weak-colimit algebraic-structure API uses bijectivity on morphisms and
filtered stalks; the ordinary-stalk companion is available when all colimits exist. -/
@[stacks 00AH "pushforward along a closed subset is fully faithful"]
#check TopCat.Sheaf.Subset.map_bijective

@[stacks 00AH "essential image characterized by terminal stalks off the closed subset"]
#check TopCat.Sheaf.ClosedSubset.essImage_iff_filteredStalk_isTerminal_of_not_mem

#check TopCat.Sheaf.ClosedSubset.essImage_iff_stalk_isTerminal_of_not_mem
