/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.Taut.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open Algebra.TensorProduct

namespace RingHom

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
variable [Algebra A B] [Algebra A C]

/- Lemma 87.5.6: Let `algebraMap A B` and `algebraMap A C` be continuous
homomorphisms of linearly topologized rings. If `algebraMap A B` is taut, then
`Completed.includeRight A B C` is taut. -/
@[stacks 0GX5] #check (RingHom.IsTaut.completedTensor_includeRight :
  Continuous (algebraMap A B) → Continuous (algebraMap A C) →
    (algebraMap A B).IsTaut → (Algebra.TensorProduct.Completed.includeRight A B C).IsTaut)

end RingHom
