/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap100.Lemma_100_9_11_Pullback
public import stacks_project.Chap100.Lemma_100_9_11_Substack

/-!
# Locally closed substacks of a presentation

A presentation `[U / R] ⟶ X` of an algebraic stack identifies locally closed
substacks of `X` with `R`-invariant locally closed subspaces of `U` by sending
`Z` to `U ×_X Z`. A morphism of algebraic stacks `Y ⟶ X` factors through `Z`
if and only if `Y ×_X U ⟶ U` factors through that subspace. The same
correspondence holds for closed and open substacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Presentation

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Lemma 100.9.11 (1): Let `[U / R] ⟶ X` be a presentation of an algebraic
stack. Sending a locally closed substack `Z` of `X` to the `R`-invariant
locally closed subspace `U ×_X Z` of `U`, then taking the strictly full image
of `[Z / R_Z] ⟶ X`, recovers `Z` as an `objectProperty` of `X`. -/
@[stacks 0507]
theorem ofInvariantSubspace_pullbackSubspace (P : Presentation X)
    (Z : LocallyClosedSubstack X) :
    (P.ofInvariantSubspace (P.pullbackSubspace Z)
        (isLocallyClosedInvariant_pullbackSubspace P Z)).objectProperty =
      Z.objectProperty :=
  sorry

/-- Lemma 100.9.11 (2): A morphism of algebraic stacks `f : Y ⟶ X` factors
through a locally closed substack `Z` if and only if `Y ×_X U ⟶ U` factors
through the corresponding `R`-invariant locally closed subspace of `U`. -/
@[stacks 0507]
theorem factorsThrough_iff {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : Presentation X) (Z : LocallyClosedSubstack X) (f : Y ⟶ X) :
    FactorsThrough f Z.ι ↔
      FactorsThrough (P.objectProjection f)
        (toGroupoids.map (P.pullbackSubspace Z).ι) :=
  sorry

/-- Lemma 100.9.11 (3): Sending a closed substack `Z` of `X` to the
`R`-invariant closed subspace `U ×_X Z` of `U`, then taking the strictly full
image of `[Z / R_Z] ⟶ X`, recovers `Z` as an `objectProperty` of `X`. -/
@[stacks 0507]
theorem ofInvariantClosedSubspace_pullbackClosedSubspace (P : Presentation X)
    (Z : ClosedSubstack X) :
    (P.ofInvariantClosedSubspace (P.pullbackClosedSubspace Z)
        (isLocallyClosedInvariant_pullbackClosedSubspace P Z)).objectProperty =
      Z.objectProperty :=
  sorry

/-- Lemma 100.9.11 (4): A morphism of algebraic stacks `f : Y ⟶ X` factors
through a closed substack `Z` if and only if `Y ×_X U ⟶ U` factors through the
corresponding `R`-invariant closed subspace of `U`. -/
@[stacks 0507]
theorem closed_factorsThrough_iff {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : Presentation X) (Z : ClosedSubstack X) (f : Y ⟶ X) :
    FactorsThrough f Z.ι ↔
      FactorsThrough (P.objectProjection f)
        (toGroupoids.map (P.pullbackClosedSubspace Z).ι) :=
  sorry

/-- Lemma 100.9.11 (5): Sending an open substack `Z` of `X` to the
`R`-invariant open subspace `U ×_X Z` of `U`, then taking the strictly full
image of `[Z / R_Z] ⟶ X`, recovers `Z` as an `objectProperty` of `X`. -/
@[stacks 0507]
theorem ofInvariantOpenSubspace_pullbackOpenSubspace (P : Presentation X)
    (Z : OpenSubstack X) :
    (P.ofInvariantOpenSubspace (P.pullbackOpenSubspace Z)
        (isOpenInvariant_pullbackOpenSubspace P Z)).objectProperty =
      Z.objectProperty :=
  sorry

/-- Lemma 100.9.11 (6): A morphism of algebraic stacks `f : Y ⟶ X` factors
through an open substack `Z` if and only if `Y ×_X U ⟶ U` factors through the
corresponding `R`-invariant open subspace of `U`. -/
@[stacks 0507]
theorem open_factorsThrough_iff {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : Presentation X) (Z : OpenSubstack X) (f : Y ⟶ X) :
    FactorsThrough f Z.ι ↔
      FactorsThrough (P.objectProjection f)
        (toGroupoids.map (P.pullbackOpenSubspace Z).ι) :=
  sorry

/-- An `R`-invariant locally closed subspace of `U` is recovered, up to an
isomorphism over `U`, as `U ×_X` of the associated locally closed substack. -/
theorem pullbackSubspace_ofInvariantSubspace (P : Presentation X)
    (Z : LocallyClosedSubspace P.groupoid.U.left)
    (hZ : P.groupoid.IsLocallyClosedInvariant Z) :
    ∃ e : (P.pullbackSubspace (P.ofInvariantSubspace Z hZ)).X ≅ Z.X,
      e.hom ≫ Z.ι = (P.pullbackSubspace (P.ofInvariantSubspace Z hZ)).ι :=
  sorry

/-- An `R`-invariant closed subspace of `U` is recovered, up to an isomorphism
over `U`, as `U ×_X` of the associated closed substack. -/
theorem pullbackClosedSubspace_ofInvariantClosedSubspace (P : Presentation X)
    (C : ClosedSubspace P.groupoid.U.left)
    (hC : P.groupoid.IsLocallyClosedInvariant C.toLocallyClosed) :
    ∃ e : (P.pullbackClosedSubspace (P.ofInvariantClosedSubspace C hC)).X ≅ C.X,
      e.hom ≫ C.ι =
        (P.pullbackClosedSubspace (P.ofInvariantClosedSubspace C hC)).ι :=
  sorry

/-- An `R`-invariant open subspace of `U` is recovered, up to an isomorphism
over `U`, as `U ×_X` of the associated open substack. -/
theorem pullbackOpenSubspace_ofInvariantOpenSubspace (P : Presentation X)
    (W : OpenSubspace P.groupoid.U.left) (hW : P.groupoid.IsOpenInvariant W) :
    ∃ e : (P.pullbackOpenSubspace (P.ofInvariantOpenSubspace W hW)).X ≅ W.X,
      e.hom ≫ W.ι =
        (P.pullbackOpenSubspace (P.ofInvariantOpenSubspace W hW)).ι :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Presentation
