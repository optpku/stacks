/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Algebra.Algebra
public import stacks_project.Chap87.Lemma_87_4_12_Completed
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»

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

/-- If `A` and `C` are weakly pre-admissible, then the completed tensor
`Completed B A C` is weakly admissible. -/
instance instIsWeaklyAdmissibleRing
    [TopologicalRing.IsWeaklyPreadmissibleRing A]
    [TopologicalRing.IsWeaklyPreadmissibleRing C] :
    TopologicalRing.IsWeaklyAdmissibleRing (Completed B A C) :=
  isWeaklyAdmissibleRing (continuous_algebraMap B A) (continuous_algebraMap B C)

/-- If `A` and `C` have countably generated neighbourhoods of zero, then so
does `Completed B A C`. -/
instance instNhdsZeroIsCountablyGenerated
    [IsTopologicalRing A] [IsLinearTopology A A]
    [IsTopologicalRing C] [IsLinearTopology C C]
    [(nhds (0 : A)).IsCountablyGenerated]
    [(nhds (0 : C)).IsCountablyGenerated] :
    (nhds (0 : Completed B A C)).IsCountablyGenerated :=
  isCountablyGenerated_nhds (continuous_algebraMap B A) (continuous_algebraMap B C)

/-- If `A` and `C` are countably indexed, then so is `Completed B A C`. -/
instance instIsCountablyIndexed
    [IsTopologicalRing A] [IsLinearTopology A A]
    [IsTopologicalRing C] [IsLinearTopology C C]
    [TopologicalRing.IsCountablyIndexed A]
    [TopologicalRing.IsCountablyIndexed C] :
    TopologicalRing.IsCountablyIndexed (Completed B A C) := sorry

end Algebra.TensorProduct.Completed
