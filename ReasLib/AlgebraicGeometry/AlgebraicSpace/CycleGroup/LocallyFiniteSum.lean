/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic

/-!
# Locally finite sums of dimension-supported cycles on algebraic spaces

Coefficientwise locally finite sums preserve the dimension support of cycles.
The indexing family may lie in a universe independent of the algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)

/-- The pointwise sum of a locally finite family of `k`-cycles is again a
`k`-cycle. -/
theorem locallyFiniteSum_mem {I : Type v} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support) :
    AlgebraicCycle.locallyFiniteSum
      (fun i ↦ (α i : Function.locallyFinsupp (Points X) ℤ)) hα ∈
        (cycleGroup f δ k) :=
  sorry

/-- The locally finite sum of a family of `k`-cycles whose coefficient supports
form a locally finite collection. -/
noncomputable def locallyFiniteSum {I : Type v} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support) :
    (cycleGroup f δ k) :=
  ⟨AlgebraicCycle.locallyFiniteSum
    (fun i ↦ (α i : Function.locallyFinsupp (Points X) ℤ)) hα,
    locallyFiniteSum_mem f δ k α hα⟩

/-- A coefficient of a locally finite sum of `k`-cycles is the corresponding
pointwise finite sum of coefficients. -/
theorem locallyFiniteSum_apply {I : Type v} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support)
    (x : Points X) :
    (locallyFiniteSum f δ k α hα : Function.locallyFinsupp (Points X) ℤ) x =
      ∑ᶠ i, (α i : Function.locallyFinsupp (Points X) ℤ) x :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
