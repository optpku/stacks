module

public import ReasLib.Topology.Spectral.FinitePresentation
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.14: spectral spaces are exactly directed inverse limits of finite
`T₀` spaces, up to homeomorphism. -/
@[stacks 09XX]
#check SpectralSpace.iff_homeomorphic_directedLimit_finiteT0
