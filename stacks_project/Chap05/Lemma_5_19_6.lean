module

public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Lemma 5.19.6 (1): images of specialization-stable subsets are stable under
specialization along a specialization-lifting map. -/
@[stacks 0065 "images of specialization-stable subsets"]
#check fun {f : X → Y} (_ : Continuous f) (hlift : SpecializingMap f)
    {T : Set X} (hT : StableUnderSpecialization T) ↦
  hlift.stableUnderSpecialization_image hT

/- Lemma 5.19.6 (2): images of generalization-stable subsets are stable under
generalization along a generalization-lifting map. -/
@[stacks 0065 "images of generalization-stable subsets"]
#check fun {f : X → Y} (_ : Continuous f) (hlift : GeneralizingMap f)
    {T : Set X} (hT : StableUnderGeneralization T) ↦
  hlift.stableUnderGeneralization_image hT
