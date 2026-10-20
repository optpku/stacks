module

public import ReasLib.Topology.Spectral.FiniteLimit
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.12: a directed inverse limit of finite sober spaces is spectral;
finite `T₀` stages are the canonical Lean formulation. -/
@[stacks 09XV]
#check TopCat.spectralSpace_limit_of_directed_finite_t0
