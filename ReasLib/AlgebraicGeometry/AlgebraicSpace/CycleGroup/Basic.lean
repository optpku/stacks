/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.RelativeFunction

/-!
# Dimension-supported cycles on algebraic spaces

A cycle on an algebraic space is a locally finite integer combination of points
of `|X|`. The `k`-cycles are the additive subgroup of those cycles whose nonzero
coefficients lie only at points of a prescribed dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The zero cycle has no nonzero coefficients outside any prescribed dimension. -/
private theorem cycleDimensionSubgroup_zero_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) :
    ∀ x, (0 : Function.locallyFinsupp (Points X) ℤ) x ≠ 0 → d x = k := by
  intro x hx
  exact (hx rfl).elim

/-- The sum of two cycles supported at points of dimension `k` is supported at
points of dimension `k`. -/
private theorem cycleDimensionSubgroup_add_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) {α β : Function.locallyFinsupp (Points X) ℤ}
    (hα : ∀ x, α x ≠ 0 → d x = k) (hβ : ∀ x, β x ≠ 0 → d x = k) :
    ∀ x, (α + β) x ≠ 0 → d x = k := by
  intro x hx
  change α x + β x ≠ 0 at hx
  by_cases h : α x = 0
  · exact hβ x (by simpa [h] using hx)
  · exact hα x h

/-- The negation of a cycle supported at points of dimension `k` is supported at
points of dimension `k`. -/
private theorem cycleDimensionSubgroup_neg_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) {α : Function.locallyFinsupp (Points X) ℤ}
    (hα : ∀ x, α x ≠ 0 → d x = k) :
    ∀ x, (-α) x ≠ 0 → d x = k := by
  intro x hx
  change -(α x) ≠ 0 at hx
  exact hα x (neg_ne_zero.mp hx)

/-- The additive subgroup of locally finite cycles on `|X|` whose nonzero
coefficients occur only at points of dimension `k` according to `d`. -/
noncomputable def cycleDimensionSubgroup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) where
  carrier := {α | ∀ x, α x ≠ 0 → d x = k}
  zero_mem' := by exact cycleDimensionSubgroup_zero_mem d k
  add_mem' := by exact cycleDimensionSubgroup_add_mem d k
  neg_mem' := by exact cycleDimensionSubgroup_neg_mem d k

/-- Membership in `cycleDimensionSubgroup d k` means that every point with a
nonzero coefficient has dimension `k`. -/
theorem mem_cycleDimensionSubgroup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ cycleDimensionSubgroup d k ↔ ∀ x, α x ≠ 0 → d x = k :=
  Iff.rfl

/-- A cycle in `cycleDimensionSubgroup d k` vanishes at every point whose
dimension is not `k`. -/
theorem apply_eq_zero_of_dimension_ne {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) {α : Function.locallyFinsupp (Points X) ℤ}
    (hα : α ∈ cycleDimensionSubgroup d k) {x : Points X} (hx : d x ≠ k) :
    α x = 0 := by
  by_contra h
  exact hx ((mem_cycleDimensionSubgroup d k α).mp hα x h)

/-- The closures of the support points of a locally finite cycle form a locally
finite family of closed subsets of `|X|`. -/
theorem locallyFinite_support_closures {S : Scheme.{u}} {X : AlgebraicSpace S}
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : α.support ↦ closure ({x.val} : Set (Points X)) := by
  exact (LocallyFiniteSupport.locallyFinite_support α.toFun α.locallyFiniteSupport).closure

namespace Hom

/-- The abelian group `Z_k(X)` of `k`-cycles on `X`, relative to the dimension
function `δ_{X/B}` induced by `f` and `δ`. -/
noncomputable abbrev cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) :=
  cycleDimensionSubgroup ((relativeDimensionFunction f) δ) k

/-- Membership in `(cycleGroup f) δ k` means that every nonzero coefficient of `α`
occurs at a point of relative dimension `k`. -/
theorem mem_cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ (cycleGroup f) δ k ↔
      ∀ x, α x ≠ 0 → (relativeDimensionFunction f) δ x = k :=
  Iff.rfl

end Hom

end AlgebraicGeometry.AlgebraicSpace
