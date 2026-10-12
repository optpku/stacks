/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap76.Lemma_76_32_2_DimensionFunction

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

/-- The additive subgroup of locally finite cycles on `|X|` whose nonzero
coefficients occur only at points of dimension `k` according to `d`. -/
noncomputable def cycleDimensionSubgroup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) where
  carrier := {α | ∀ x, α x ≠ 0 → d x = k}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in `cycleDimensionSubgroup d k` means that every point with a
nonzero coefficient has dimension `k`. -/
theorem mem_cycleDimensionSubgroup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ cycleDimensionSubgroup d k ↔ ∀ x, α x ≠ 0 → d x = k :=
  sorry

/-- A cycle in `cycleDimensionSubgroup d k` vanishes at every point whose
dimension is not `k`. -/
theorem apply_eq_zero_of_dimension_ne {S : Scheme.{u}} {X : AlgebraicSpace S}
    (d : Points X → ℤ) (k : ℤ) {α : Function.locallyFinsupp (Points X) ℤ}
    (hα : α ∈ cycleDimensionSubgroup d k) {x : Points X} (hx : d x ≠ k) :
    α x = 0 :=
  sorry

/-- The closures of the support points of a locally finite cycle form a locally
finite family of closed subsets of `|X|`. -/
theorem locallyFinite_support_closures {S : Scheme.{u}} {X : AlgebraicSpace S}
    (α : Function.locallyFinsupp (Points X) ℤ) :
    LocallyFinite fun x : α.support ↦ closure ({x.val} : Set (Points X)) :=
  sorry

namespace Hom

/-- The abelian group `Z_k(X)` of `k`-cycles on `X`, relative to the dimension
function `δ_{X/B}` induced by `f` and `δ`. -/
noncomputable abbrev cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) (δ : Points B → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) :=
  cycleDimensionSubgroup ((relativeDimensionFunction f) δ) k

/-- Membership in `(cycleGroup f) δ k` means that every nonzero coefficient of `α`
occurs at a point of relative dimension `k`. -/
theorem mem_cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) (δ : Points B → ℤ) (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ (cycleGroup f) δ k ↔
      ∀ x, α x ≠ 0 → (relativeDimensionFunction f) δ x = k :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
