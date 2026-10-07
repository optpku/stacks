module

public import ReasLib.Topology.Spectral.Sierpinski
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.13: the compact-open membership map gives the canonical
constructibly closed Sierpinski-product presentation of a spectral space. -/
@[stacks 09XW]
#check SpectralSpace.iff_homeomorphic_constructiblyClosed_sierpinskiProduct
