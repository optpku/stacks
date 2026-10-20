module

public import ReasLib.Topology.Spectral.CompactOpenIntersection
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.24.7 is now owned by the topology-neutral compact-open intersection API and its spectral
extension. The source path remains a tagged reference surface for the four textbook clauses.
-/

/- Lemma 5.24.7 (1): equivalent compact-generalizing presentations. -/
@[stacks 0A31 "five equivalent compact-generalizing presentations"]
#check compactGeneralizingSubset_tfae

/- Lemma 5.24.7 (2): spectrality of a directed compact-open intersection. -/
@[stacks 0A31 "spectrality of the intersection"]
#check IsCompactOpenDirectedIntersection.spectralSpace

/- Lemma 5.24.7 (3): inverse-limit presentation of the intersection. -/
@[stacks 0A31 "inverse-limit presentation"]
#check IsCompactOpenDirectedIntersection.cone_limitProperty

/- Lemma 5.24.7 (4): a compact-open stage lies in every open neighbourhood. -/
@[stacks 0A31 "a stage lies in every open neighborhood"]
#check IsCompactOpenDirectedIntersection.exists_compactOpen_subset_of_isOpen
