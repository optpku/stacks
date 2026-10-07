module

public import ReasLib.Topology.Sober.Kolmogorov
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.16

The soberification and Kolmogorov-reflection APIs are owned by the corresponding
`ReasLib.Topology.IrreducibleCloseds.Soberification` and `ReasLib.Topology.Sober` leaves.
-/

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.8.16 (1): the point-closure map is universal for continuous maps into sober spaces. -/
@[stacks 0A2N "universal property for sober targets"]
#check @toIrreducibleCloseds_universal

/- Lemma 5.8.16 (2): inverse image along the point-closure map is bijective on opens. -/
@[stacks 0A2N "bijection and frame operations on opens"]
#check @toIrreducibleCloseds_opensComap_bijective

/- Lemma 5.8.16 (3): the image is Kolmogorov by the inherited subtype instance. -/
@[stacks 0A2N "Kolmogorov image"]
#check (inferInstance : T0Space (Set.range (toIrreducibleCloseds : X → IrreducibleCloseds X)))

/- Lemma 5.8.16 (4): the point-closure map into its range is universal for continuous maps into
Kolmogorov spaces. -/
@[stacks 0A2N "universal property of the Kolmogorov image"]
#check @toIrreducibleClosedsImage_universal
