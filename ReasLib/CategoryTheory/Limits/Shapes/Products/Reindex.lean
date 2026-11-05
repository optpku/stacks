/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Shapes.Products.Diagonal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing constant products

The functor `Pi.diagonal` takes a product of copies of an object, assuming only these
constant products exist.
A function of indexing types induces the contravariant reindexing natural transformation.  This
is the categorical product-projection API used by finite coskeleton calculations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w' w v u

namespace CategoryTheory.Limits.Pi.diagonal

variable {C : Type u} [Category.{v} C]

/-- The component of contravariant power reindexing along `tau : S' → S`. -/
noncomputable def reindexApp {S : Type w} {S' : Type w'}
    [∀ X : C, HasProduct (fun _ : S ↦ X)]
    [∀ X : C, HasProduct (fun _ : S' ↦ X)]
    (tau : S' → S) (X : C) :
    (∏ᶜ fun _ : S ↦ X) ⟶ (∏ᶜ fun _ : S' ↦ X) :=
  Pi.lift (fun s' ↦ Pi.π (fun _ : S ↦ X) (tau s'))

/-- The component of reindexing followed by a projection selects the original factor. -/
@[reassoc (attr := simp)]
theorem reindexApp_π {S : Type w} {S' : Type w'}
    [∀ X : C, HasProduct (fun _ : S ↦ X)]
    [∀ X : C, HasProduct (fun _ : S' ↦ X)]
    (tau : S' → S) (X : C) (s' : S') :
    reindexApp (C := C) tau X ≫ Pi.π (fun _ : S' ↦ X) s' =
      Pi.π (fun _ : S ↦ X) (tau s') :=
  Pi.lift_π _ s'

/-- Power reindexing is natural in the repeated object. -/
theorem reindexApp_naturality {S : Type w} {S' : Type w'}
    [∀ X : C, HasProduct (fun _ : S ↦ X)]
    [∀ X : C, HasProduct (fun _ : S' ↦ X)]
    (tau : S' → S) {X Y : C} (f : X ⟶ Y) :
    (Pi.diagonal (C := C) S).map f ≫ reindexApp tau Y =
      reindexApp tau X ≫ (Pi.diagonal (C := C) S').map f := by
  apply Pi.hom_ext
  intro s'
  simp [reindexApp, Category.assoc, Pi.lift_π, Pi.lift_π_assoc]

/-- A function `S' → S` induces the natural projection from `S`-indexed powers to
`S'`-indexed powers. -/
@[stacks 01GJ "constant product reindexing"]
noncomputable def reindex {S : Type w} {S' : Type w'}
    [∀ X : C, HasProduct (fun _ : S ↦ X)]
    [∀ X : C, HasProduct (fun _ : S' ↦ X)]
    (tau : S' → S) : Pi.diagonal (C := C) S ⟶ Pi.diagonal (C := C) S' where
  app X := reindexApp tau X
  naturality _ _ f := reindexApp_naturality tau f

/-- The component of `reindex tau` is the corresponding product projection. -/
@[simp]
theorem reindex_app {S : Type w} {S' : Type w'}
    [∀ X : C, HasProduct (fun _ : S ↦ X)]
    [∀ X : C, HasProduct (fun _ : S' ↦ X)]
    (tau : S' → S) (X : C) :
    (reindex (C := C) tau).app X = reindexApp tau X := rfl

/-- Reindexing followed by projection at `s'` is projection at `tau s'`. -/
@[reassoc (attr := simp)]
theorem reindex_π {S : Type w} {S' : Type w'}
    [∀ X : C, HasProduct (fun _ : S ↦ X)]
    [∀ X : C, HasProduct (fun _ : S' ↦ X)]
    (tau : S' → S) (X : C) (s' : S') :
    (reindex (C := C) tau).app X ≫ Pi.π (fun _ : S' ↦ X) s' =
      Pi.π (fun _ : S ↦ X) (tau s') :=
  reindexApp_π tau X s'

end CategoryTheory.Limits.Pi.diagonal
