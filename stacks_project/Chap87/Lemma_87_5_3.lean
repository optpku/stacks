module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_5_3_Completion

/-!
# Lemma 87.5.3

The canonical map from a linearly topologized ring to its inverse-limit completion is taut.
-/

@[expose] public section

universe u

open IsLinearTopology

namespace RingHom

variable {A : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- Lemma 87.5.3: Let `A` be a linearly topologized ring. The map `A → Completion A A`
from `A` to its completion is taut. -/
@[stacks 0GX2]
theorem IsTaut.completion : (Completion.coeRingHom : A →+* Completion A A).IsTaut :=
  sorry

end RingHom
