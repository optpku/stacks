module

public import ReasLib.Topology.Specialization.Dimension.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.20.2

Dimension-function catenarity and codimension APIs are owned by
`ReasLib.Topology.Specialization.Dimension.Catenary`.
-/

/- Lemma 5.20.2: the reusable quasi-sober catenarity consequence. -/
@[stacks 02IA "catenarity from a dimension function"]
#check @IsDimensionFunction.catenarySpace

/- Lemma 5.20.2: the reusable quasi-sober point-closure codimension formula. -/
@[stacks 02IA "codimension formula for specialized point closures"]
#check @IsDimensionFunction.sub_eq_codimBetween_pointClosure

/- Lemma 5.20.2 (1): the sober catenarity consequence. -/
@[stacks 02IA "catenarity from a dimension function"]
#check @IsDimensionFunction.catenarySpace_of_sober

/- Lemma 5.20.2 (2): the sober point-closure codimension formula. -/
@[stacks 02IA "codimension formula for specialized point closures"]
#check @IsDimensionFunction.sub_eq_codimBetween_pointClosure_of_sober
