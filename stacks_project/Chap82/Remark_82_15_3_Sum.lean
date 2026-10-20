module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup

/-!
# Geometric support and locally finite sums of algebraic-space cycles

This file records the geometric support of a locally finite cycle on `|X|` and
the locally finite sum of a family of `k`-cycles.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The geometric support of a cycle, as the union of closures of points with
nonzero coefficient. -/
def cycleGeometricSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (α : Function.locallyFinsupp (Points X) ℤ) : Set (Points X) :=
  ⋃ x ∈ α.support, closure ({x} : Set (Points X))

/-- A point lies in the geometric support of a cycle if and only if it lies in
the closure of some point of the coefficient support. -/
theorem mem_cycleGeometricSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (α : Function.locallyFinsupp (Points X) ℤ) (x : Points X) :
    x ∈ cycleGeometricSupport α ↔
      ∃ y ∈ α.support, x ∈ closure ({y} : Set (Points X)) :=
  sorry

/-- For a closed set `T`, the geometric support of a cycle is contained in `T`
if and only if the coefficient support is contained in `T`. -/
theorem cycleGeometricSupport_subset_closed_iff {S : Scheme.{u}}
    {X : AlgebraicSpace S} (α : Function.locallyFinsupp (Points X) ℤ)
    (T : Closeds (Points X)) :
    cycleGeometricSupport α ⊆ T.carrier ↔ α.support ⊆ T.carrier :=
  sorry

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)

/-- The pointwise sum of a locally finite family of `k`-cycles is again a
`k`-cycle. -/
theorem locallyFiniteSum_mem {I : Type u} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support) :
    AlgebraicCycle.locallyFiniteSum
      (fun i ↦ (α i : Function.locallyFinsupp (Points X) ℤ)) hα ∈
        (cycleGroup f δ k) :=
  sorry

/-- The locally finite sum of a family of `k`-cycles whose coefficient supports
form a locally finite collection. -/
noncomputable def locallyFiniteSum {I : Type u} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support) :
    (cycleGroup f δ k) :=
  ⟨AlgebraicCycle.locallyFiniteSum
    (fun i ↦ (α i : Function.locallyFinsupp (Points X) ℤ)) hα,
    locallyFiniteSum_mem f δ k α hα⟩

/-- A coefficient of a locally finite sum of `k`-cycles is the corresponding
pointwise finite sum of coefficients. -/
theorem locallyFiniteSum_apply {I : Type u} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support)
    (x : Points X) :
    (locallyFiniteSum f δ k α hα : Function.locallyFinsupp (Points X) ℤ) x =
      ∑ᶠ i, (α i : Function.locallyFinsupp (Points X) ℤ) x :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
