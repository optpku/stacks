module

public import ReasLib.RingTheory.Smooth.Adic.Topology
import StacksCheckRecall

/-!
# Lemma 15.37.2 (07EC)

@stack 07EC
-/

@[expose] public section

/- Lemma 15.37.2 (1) (07EC): algebraic formal smoothness implies topological formal
smoothness for a continuous map from a linearly topologized ring to a pre-adic ring. -/
@[stacks 07EC "(1), algebraic formal smoothness implies topological formal smoothness"]
#check @RingHom.FormallySmooth.toTopologically

/- Lemma 15.37.2 (2) (07EC): the source adic topology may be replaced by the discrete topology. -/
@[stacks 07EC "(2), independence of the source adic topology"]
#check @RingHom.formallySmoothTopologically_adicSource_iff_discreteSource
