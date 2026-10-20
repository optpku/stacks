module

public import ReasLib.Topology.Sheaf.Subset
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} {Z : Set X}

/- Lemma 6.32.2: the arbitrary-subset fully-faithful owner strengthens the closed-subset
statement, and the essential-image criterion is the set-valued closed-subset specialization. -/
@[stacks 00AF "pushforward of set-valued sheaves along a closed subset is fully faithful"]
#check TopCat.Sheaf.Subset.fullyFaithful

@[stacks 00AF "essential image consists of sheaves with singleton stalks off the closed subset"]
#check TopCat.Sheaf.ClosedSubset.type_essImage_iff_stalk_isTerminal_of_not_mem
