/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation

/-!
# Augmentation functors with coefficients

An augmentation of simplicial spaces induces inverse and direct image functors on
sheaves with coefficients. For sets, these agree with the geometric augmentation functors.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open Functor
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}}

/-- Inverse image `a⁻¹` along the Zariski augmentation of a simplicial space. -/
def inverseImage {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P] :
    Sheaf (Opens.grothendieckTopology X) B ⥤ Sheaf (zariskiTopology Y) B :=
  (constProjection X).sheafPushforwardContinuous B
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) ⋙
    (zariskiMap a).sheafPullback B (zariskiTopology (constSpace X)) (zariskiTopology Y)

/-- `inverseImage` is the composite of continuous pushforward along `constProjection` with
sheaf pullback along `zariskiMap a`. -/
theorem inverseImage_eq {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P] :
    inverseImage a B =
      (constProjection X).sheafPushforwardContinuous B
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) ⋙
        (zariskiMap a).sheafPullback B (zariskiTopology (constSpace X)) (zariskiTopology Y) :=
  rfl

/-- Direct image `a_*` along the Zariski augmentation of a simplicial space. -/
def directImage {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    Sheaf (zariskiTopology Y) B ⥤ Sheaf (Opens.grothendieckTopology X) B :=
  (zariskiMap a).sheafPushforwardContinuous B
      (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
    (constProjection X).sheafPushforwardCocontinuous B
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)

/-- `directImage` is the composite of continuous pushforward along `zariskiMap a` with
cocontinuous pushforward along `constProjection`. -/
theorem directImage_eq {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    directImage a B =
      (zariskiMap a).sheafPushforwardContinuous B
          (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
        (constProjection X).sheafPushforwardCocontinuous B
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) :=
  rfl

/-- Inverse image is left adjoint to direct image along a Zariski augmentation. -/
def inverseImageAdjunction {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    inverseImage a B ⊣ directImage a B :=
  ((constProjection X).sheafAdjunctionCocontinuous B
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).comp
    ((zariskiMap a).sheafAdjunctionContinuous B
      (zariskiTopology (constSpace X)) (zariskiTopology Y))

/-- Inverse image of set-valued sheaves along an augmentation is canonically
isomorphic to the inverse image of its geometric morphism. -/
public def inverseImageIso_augmentation {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    inverseImage a (Type u) ≅ (augmentationMorphism a)⁻¹ :=
  isoWhiskerRight (constMorphism_inverseImage_iso X).symm
    ((zariskiMap a).sheafPullback (Type u)
      (zariskiTopology (constSpace X)) (zariskiTopology Y))

/-- The augmentation inverse-image comparison is obtained by whiskering the inverse
of the constant-space inverse-image comparison with sheaf pullback. -/
public theorem inverseImageIso_augmentation_hom {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    (inverseImageIso_augmentation a).hom =
      whiskerRight (constMorphism_inverseImage_iso X).inv
        ((zariskiMap a).sheafPullback (Type u)
          (zariskiTopology (constSpace X)) (zariskiTopology Y)) :=
  rfl

/-- Coefficient inverse image and geometric inverse image along an augmentation
have the same essential image on set-valued sheaves. -/
public theorem mem_essImage_inverseImage_iff_augmentation {X : TopCat.{u}}
    (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    (inverseImage a (Type u)).essImage G ↔ (augmentationMorphism a)⁻¹.essImage G :=
  sorry

/-- Direct image of type-valued sheaves along a Zariski augmentation is
`(augmentationMorphism a)_*`. -/
theorem directImage_eq_augmentation {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    [HasWeakSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    directImage a (Type u) = (augmentationMorphism a).pushforward :=
  rfl

end CategoryTheory.SimplicialObject

end
