/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FirstOrderThickening
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# First-order thickening presentation adapters

The legacy strictly-full predicate records full faithfulness of the total
functor. These adapters identify it with the fields of the map-level
first-order thickening presentation property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening

/-- A first-order thickening presentation has a full and faithful total functor
in the legacy strictly-full predicate. -/
instance toIsStrictlyFull {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [h : IsFirstOrderThickening i] : Groupoids.Hom.IsStrictlyFull i where
  full := h.full
  faithful := h.faithful

/-- A morphism with a full and faithful total functor that is a first-order
thickening of groupoid fibrations is a first-order thickening presentation. -/
instance of_hom {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [h_fot : Groupoids.Hom.IsFirstOrderThickening i]
    [h_full : Groupoids.Hom.IsStrictlyFull i] : IsFirstOrderThickening i where
  toIsFirstOrderThickening := h_fot
  full := h_full.full
  faithful := h_full.faithful

/-- A morphism is a first-order thickening presentation if and only if it is
legacy strictly full and a first-order thickening of groupoid fibrations. -/
theorem iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') :
    IsFirstOrderThickening i ↔
      Groupoids.Hom.IsStrictlyFull i ∧
        Groupoids.Hom.IsFirstOrderThickening i := by
  constructor
  · intro h
    exact ⟨⟨h.full, h.faithful⟩, h.toIsFirstOrderThickening⟩
  · rintro ⟨h_full, h_fot⟩
    exact { toIsFirstOrderThickening := h_fot
            full := h_full.full
            faithful := h_full.faithful }

/-- A first-order thickening presentation is a legacy strictly-full closed
immersion with the algebraic-space first-order-thickening property on
scheme-slice representing morphisms. -/
theorem spec {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    Groupoids.Hom.ClosedImmersion i ∧ Groupoids.Hom.IsStrictlyFull i ∧
      Groupoids.Hom.has (@AlgebraicSpace.IsFirstOrderThickening S) i :=
  ⟨Groupoids.Hom.IsFirstOrderThickening.instClosedImmersion i,
    toIsStrictlyFull i, Groupoids.Hom.IsFirstOrderThickening.has_isFirstOrderThickening i⟩

end AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening

#check (AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'], (X ⟶ X') → Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsFirstOrderThickening.iff :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X'),
    AlgebraicStack.IsFirstOrderThickening i ↔
      Groupoids.Hom.IsStrictlyFull i ∧ Groupoids.Hom.IsFirstOrderThickening i)
