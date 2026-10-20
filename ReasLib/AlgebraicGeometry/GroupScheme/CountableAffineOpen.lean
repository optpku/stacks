/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Topology

/-!
# Countable affine opens in group schemes

This file constructs a clopen countable union of affine opens containing the identity of a group
scheme over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Every group scheme over a field contains its identity point in a clopen open subscheme that
is a countable union of affine opens. -/
theorem existsClopenCountableAffineCover {k : Type u} [Field k]
    (G : SchemeOverField k) [GrpObj G] :
    ∃ U : G.left.Opens,
      η[G].left (IsLocalRing.closedPoint k) ∈ (U : Set G.left) ∧ IsClopen (U : Set G.left) ∧
      ∃ V : ℕ → G.left.Opens, (∀ n, IsAffineOpen (V n)) ∧ iSup V = U := by
  -- Source argument (Stacks 047U): take a quasi-compact inverse-stable open `U ∋ e`; the union
  -- `⋃ₙ mₙ(U × ⋯ × U)` of the open images of the `n`-fold multiplication maps is an open
  -- subgroup, hence closed. The identity component need not be open here.
  sorry

end AlgebraicGeometry.GroupScheme
