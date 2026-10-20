/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Composition.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Computations for sequential postcomposition coherence

This leaf exposes the equivalence, strong-transformation, component, and
naturality projections of `postcompose.composition.equivalence` without requiring clients
to unfold pointwise-equivalence assembly.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {X Y Z : C}

/-- Evaluation of the sequential-postcomposition equivalence is the explicit
objectwise component equivalence. -/
@[simp]
theorem postcompose.composition.equivalence.app
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.equivalence K f g).app S =
      postcompose.composition.component.equivalence f g S := sorry

/-- The forward strong transformation of sequential-postcomposition coherence
is the explicitly assembled direct-to-successive comparison. -/
@[simp]
theorem postcompose.composition.equivalence.hom
    (K : Pseudofunctor A C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (postcompose.composition.equivalence K f g).hom =
      postcompose.composition.strongTrans K f g := sorry

/-- The forward component of sequential-postcomposition coherence is the
explicit associator-based costructured-arrow morphism. -/
@[simp]
theorem postcompose.composition.equivalence.hom.app
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.equivalence K f g).hom.app S =
      postcompose.composition.component.hom f g S := sorry

/-- The inverse component of sequential-postcomposition coherence is the
explicit inverse-associator-based costructured-arrow morphism. -/
@[simp]
theorem postcompose.composition.equivalence.inv.app
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.equivalence K f g).inv.app S =
      postcompose.composition.component.inv f g S := sorry

/-- Strong naturality of the forward sequential-postcomposition component is
the explicit `iso₂Mk` naturality comparison. -/
@[simp]
theorem postcompose.composition.equivalence.hom.naturality
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    (postcompose.composition.equivalence K f g).hom.naturality u =
      postcompose.composition.naturality f g u := sorry

/-- The forward component of sequential-postcomposition coherence has identity
source map. -/
@[simp]
theorem postcompose.composition.equivalence.hom.app.map
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Z)
        ((postcompose.composition.equivalence K f g).hom.app S) =
      𝟙 S.left := sorry

/-- The inverse component of sequential-postcomposition coherence has identity
source map. -/
@[simp]
theorem postcompose.composition.equivalence.inv.app.map
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Z)
        ((postcompose.composition.equivalence K f g).inv.app S) =
      𝟙 S.left := sorry

/-- The normalized comparison of the forward sequential-postcomposition
component is its explicit map-identity, unitor, and associator pasting. -/
@[simp]
theorem postcompose.composition.equivalence.hom.app.fac
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.fac (K := K) (X := Z)
        ((postcompose.composition.equivalence K f g).hom.app S) =
      (K.mapId S.left).hom ▷ ((S.hom ≫ f) ≫ g) ≫
        (λ_ ((S.hom ≫ f) ≫ g)).hom ≫
          (α_ S.hom f g).hom := sorry

/-- The normalized comparison of the inverse sequential-postcomposition
component is its explicit map-identity, unitor, and inverse-associator
pasting. -/
@[simp]
theorem postcompose.composition.equivalence.inv.app.fac
    {K : Pseudofunctor A C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.fac (K := K) (X := Z)
        ((postcompose.composition.equivalence K f g).inv.app S) =
      (K.mapId S.left).hom ▷ (S.hom ≫ (f ≫ g)) ≫
        (λ_ (S.hom ≫ (f ≫ g))).hom ≫
          (α_ S.hom f g).inv := sorry

/- Data audit (mathlib 4.32): this module adds no data. Its theorems expose
the explicit components and naturality already owned by the preceding leaves. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
