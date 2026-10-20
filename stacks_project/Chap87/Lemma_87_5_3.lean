/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.Taut.Completion
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 87.5.3: The canonical map from a linearly topologized ring to its
inverse-limit completion is taut. -/
@[stacks 0GX2] #check (RingHom.IsTaut.completion :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A],
    (IsLinearTopology.Completion.coeRingHom : A →+* IsLinearTopology.Completion A A).IsTaut)
