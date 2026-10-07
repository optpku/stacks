module

public import Mathlib.Topology.Category.TopCat.Limits.Konig
import StacksCheckRecall

@[expose] public section

/- Lemma 5.14.6: a cofiltered limit of nonempty compact Hausdorff spaces is
nonempty. Mathlib proves the canonical stronger cofiltered-or-empty version. -/
@[stacks 0A2R "nonemptiness of a cofiltered limit of quasi-compact Hausdorff spaces"]
#check TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system
