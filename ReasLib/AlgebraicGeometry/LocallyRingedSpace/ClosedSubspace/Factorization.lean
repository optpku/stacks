/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Pullback

/-!
# Factorization through associated closed subspaces

This leaf owns the universal factorization criterion and keeps the chosen
ideal and association evidence explicit. It exposes existence and uniqueness
without choosing a morphism from a deferred proof.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

section

variable {X Y Z : LocallyRingedSpace.{u}}
variable {I : IdealSubobject X} {i : Z ⟶ X} {f : Y ⟶ X}

/-- Lemma 26.4.6 (1): a morphism factors through an associated closed subspace exactly when
the pulled-back defining ideal map vanishes. -/
@[stacks 01HP]
theorem ClosedSubspace.IsAssociated.exists_lift_iff
    (hi : ClosedSubspace.IsAssociated i I) (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔ I.pullbackMap f = 0 := sorry

/-- A factorization through an associated closed subspace makes the pulled-back ideal map
vanish. -/
@[stacks 01HP "factorization implies pullback vanishing"]
theorem ClosedSubspace.IsAssociated.pullbackMap_eq_zero
    (hi : ClosedSubspace.IsAssociated i I)
    (g : Y ⟶ Z) (hg : g ≫ i = f) :
    I.pullbackMap f = 0 := sorry

/-- Vanishing of the pulled-back ideal map produces a factorization through the associated
closed subspace. -/
@[stacks 01HP "factorization from pullback vanishing"]
theorem ClosedSubspace.IsAssociated.exists_lift
    (hi : ClosedSubspace.IsAssociated i I)
    (hzero : I.pullbackMap f = 0) :
    ∃ g : Y ⟶ Z, g ≫ i = f := sorry

/-- Lemma 26.4.6 (2): a factorization supplied by the vanishing criterion is unique. -/
@[stacks 01HP "unique lift"]
theorem ClosedSubspace.IsAssociated.existsUnique_lift
    (hi : ClosedSubspace.IsAssociated i I)
    (hzero : I.pullbackMap f = 0) :
    ∃! g : Y ⟶ Z, g ≫ i = f := sorry

/-- Vanishing of the pulled-back ideal map is equivalent to existence of a unique
factorization through the associated closed subspace. -/
@[stacks 01HP "unique factorization criterion"]
theorem ClosedSubspace.IsAssociated.existsUnique_lift_iff
    (hi : ClosedSubspace.IsAssociated i I) (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔ I.pullbackMap f = 0 := sorry

end

end AlgebraicGeometry.LocallyRingedSpace
