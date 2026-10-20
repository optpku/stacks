/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.TensorProduct.CountablyIndexed

/-!
# Countably indexed weakly admissible completed tensors

Completed tensors of weakly pre-admissible algebras remain weakly admissible,
and countable neighbourhood bases at zero are preserved, so `Completed B A C`
stays in `WAdm^count` when `A` and `C` do.
-/

@[expose] public section

noncomputable section

universe u

open Filter Topology

namespace Algebra.TensorProduct.Completed

variable {B A C : Type u}
variable [CommRing B] [CommRing A] [CommRing C]
variable [Algebra B A] [Algebra B C]
variable [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
variable [IsTopologicalRing B] [IsLinearTopology B B]
variable [ContinuousSMul B A] [ContinuousSMul B C]

#check (Algebra.TensorProduct.Completed.instIsWeaklyAdmissibleRing :
    ∀ [TopologicalRing.IsWeaklyPreadmissibleRing A]
      [TopologicalRing.IsWeaklyPreadmissibleRing C],
      TopologicalRing.IsWeaklyAdmissibleRing (Completed B A C))

#check (Algebra.TensorProduct.Completed.instNhdsZeroIsCountablyGenerated :
    ∀ [IsTopologicalRing A] [IsLinearTopology A A]
      [IsTopologicalRing C] [IsLinearTopology C C]
      [(nhds (0 : A)).IsCountablyGenerated]
      [(nhds (0 : C)).IsCountablyGenerated],
      (nhds (0 : Completed B A C)).IsCountablyGenerated)

#check (Algebra.TensorProduct.Completed.instIsCountablyIndexed :
    ∀ [IsTopologicalRing A] [IsLinearTopology A A]
      [IsTopologicalRing C] [IsLinearTopology C C]
      [TopologicalRing.IsCountablyIndexed A]
      [TopologicalRing.IsCountablyIndexed C],
      TopologicalRing.IsCountablyIndexed (Completed B A C))

end Algebra.TensorProduct.Completed
