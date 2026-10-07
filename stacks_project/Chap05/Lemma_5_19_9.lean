module

public import ReasLib.Topology.KrullDimension.Maps
import StacksCheckRecall

@[expose] public section

/- Lemma 5.19.9: a continuous surjective map lifting either specializations or
generalizations does not increase topological Krull dimension. -/
@[stacks 02JF]
#check @Continuous.topologicalKrullDim_le_of_surjective_of_specializing_or_generalizingMap
