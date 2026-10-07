module

public import ReasLib.CategoryTheory.Sites.Canonical.Subcanonical
import StacksCheckRecall

@[expose] public section

/- Definition 7.12.2: the topology on a site C is weaker than the canonical
topology, or subcanonical, when every covering is a universal effective
epimorphism. This is `J.Subcanonical`, equivalently every covering sieve
is `Sieve.IsUniversallyEffectiveEpimorphic`. -/
@[stacks 00WQ] #check @CategoryTheory.GrothendieckTopology.subcanonical_iff_forall_cover_isUniversallyEffectiveEpimorphic

#check @CategoryTheory.GrothendieckTopology.Subcanonical
#check @CategoryTheory.Sieve.IsUniversallyEffectiveEpimorphic
