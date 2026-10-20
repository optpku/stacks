/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood

/-!
# Successor inclusions of infinitesimal neighbourhoods

Successive powers of the defining ideal induce inclusions of infinitesimal
neighbourhoods compatible with the morphisms to the ambient algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S}

/-- The defining ideal of the `(n + 1)`st infinitesimal neighbourhood is contained
in the defining ideal of the `n`th neighbourhood. -/
theorem ideal_succ_le (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    ideal i (n + 1) ≤
      ideal i n :=
  sorry

/-- The closed-subspace transition from the `n`th infinitesimal neighbourhood to
the `(n + 1)`st neighbourhood. -/
def succ (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    space i n ⟶
      space i (n + 1) :=
  inclusion (ideal_succ_le i n)

/-- Successor inclusions of infinitesimal neighbourhoods commute with their
canonical morphisms to the ambient algebraic space. -/
theorem succ_toAmbient (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    succ i n ≫ toAmbient i (n + 1) = toAmbient i n :=
  sorry

/-- For `n ≤ m`, the defining ideal of the `m`th infinitesimal neighbourhood is
contained in the defining ideal of the `n`th neighbourhood. -/
theorem ideal_le_of_le {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m) :
    ideal i m ≤ ideal i n :=
  sorry

/-- The closed-subspace inclusion `Z_n ⟶ Z_m` of infinitesimal neighbourhoods
for `n ≤ m`. -/
def transition {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m) :
    space i n ⟶ space i m :=
  inclusion (ideal_le_of_le i h)

/-- On underlying maps into the coborder, `transition i h` is the nested
closed-subspace inclusion of the neighbourhood ideals. -/
theorem transition_eq {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m) :
    transition i h = inclusion (ideal_le_of_le i h) :=
  sorry

/-- The transition `Z_n ⟶ Z_m` is a relative thickening: a closed immersion
inducing an isomorphism on reductions. -/
instance instIsThickening_transition {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m) :
    IsThickening (transition i h) :=
  sorry

/-- Postcomposing a neighbourhood transition with `toAmbient` recovers the
earlier ambient inclusion. -/
theorem transition_comp_toAmbient {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {n m : ℕ} (h : n ≤ m) :
    transition i h ≫ toAmbient i m = toAmbient i n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood
