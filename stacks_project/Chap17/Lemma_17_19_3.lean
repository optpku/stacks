module

public import ReasLib.Topology.Sheaf.InverseLimit.FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Lemma 17.19.3 (0CAK): a sheaf with a finite compact-open presentation on a spectral space
descends to a finite-stalk sheaf on a finite sober space along a spectral map. -/
@[stacks 0CAK]
#check @TopCat.Sheaf.CompactOpenPresentation.IsFinite.existsFiniteSoberModel
