/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.ChangeOfIndex
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps between pointwise left-Kan-extension colimits

A morphism in the target category reindexes the corresponding costructured-arrow categories.
This leaf specializes the general change-of-index comparison to their colimits, records its
computation on injections, and compares it with the structure map of Mathlib's chosen left Kan
extension.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftKanExtension

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {H : Type u₃} [Category.{v₃} H]
variable (L : C ⥤ D) (F : C ⥤ H)

/-- For a fully faithful functor, the unit of the chosen pointwise left Kan extension is an
isomorphism. The inverse is extracted from Mathlib's pointwise universal property, without a
family-wide left-Kan-extension hypothesis. -/
@[stacks 002K "unit isomorphism of a pointwise left Kan extension"]
noncomputable def unitIso [L.Full] [L.Faithful] [L.HasPointwiseLeftKanExtension F] :
    F ≅ L ⋙ L.leftKanExtension F :=
  @asIso _ _ _ _ (leftKanExtensionUnit L F)
    ((isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F)
      (L.leftKanExtension F) (leftKanExtensionUnit L F)).isIso_hom)

/-- The map between pointwise left-Kan-extension colimits induced by a morphism of target
objects. It is the general colimit comparison for `CostructuredArrow.map f`. -/
@[stacks 002K "map between pointwise left-Kan-extension colimits"]
noncomputable def colimitMap {X Y : D} (f : X ⟶ Y)
    [HasColimit (CostructuredArrow.proj L X ⋙ F)]
    [HasColimit (CostructuredArrow.proj L Y ⋙ F)] :
    colimit (CostructuredArrow.proj L X ⋙ F) ⟶
      colimit (CostructuredArrow.proj L Y ⋙ F) :=
  colimitComparison (H := CostructuredArrow.map f)
    (M := CostructuredArrow.proj L X ⋙ F)
    (N := CostructuredArrow.proj L Y ⋙ F) (𝟙 _)

/-- The pointwise left-Kan-extension colimit map sends an injection to the injection indexed by
postcomposition with the target morphism. -/
@[reassoc (attr := simp), stacks 002K "pointwise left-Kan-extension colimit map on injections"]
theorem colimitMap.ι {X Y : D} (f : X ⟶ Y) (g : CostructuredArrow L X)
    [HasColimit (CostructuredArrow.proj L X ⋙ F)]
    [HasColimit (CostructuredArrow.proj L Y ⋙ F)] :
    colimit.ι (CostructuredArrow.proj L X ⋙ F) g ≫ colimitMap L F f =
      colimit.ι (CostructuredArrow.proj L Y ⋙ F)
        ((CostructuredArrow.map f).obj g) := sorry

/-- The pointwise left-Kan-extension colimit map associated to an identity is the identity. -/
@[simp, stacks 002K "identity law for pointwise left-Kan-extension colimit maps"]
theorem colimitMap.id (X : D)
    [HasColimit (CostructuredArrow.proj L X ⋙ F)] :
    colimitMap L F (𝟙 X) = 𝟙 (colimit (CostructuredArrow.proj L X ⋙ F)) := sorry

/-- Pointwise left-Kan-extension colimit maps respect composition. -/
@[stacks 002K "composition law for pointwise left-Kan-extension colimit maps"]
theorem colimitMap.comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasColimit (CostructuredArrow.proj L X ⋙ F)]
    [HasColimit (CostructuredArrow.proj L Y ⋙ F)]
    [HasColimit (CostructuredArrow.proj L Z ⋙ F)] :
    colimitMap L F (f ≫ g) = colimitMap L F f ≫ colimitMap L F g := sorry

/-- When all pointwise colimits exist, `colimitMap` is the structure map of Mathlib's explicit
pointwise left Kan extension functor. -/
@[stacks 002K "comparison with Mathlib's pointwise left Kan extension map"]
theorem colimitMap.eq_pointwise [L.HasPointwiseLeftKanExtension F]
    {X Y : D} (f : X ⟶ Y) :
    colimitMap L F f = (L.pointwiseLeftKanExtension F).map f := sorry

/-- In the canonical colimit coordinates, the structure map of Mathlib's chosen left Kan
extension is the map induced by `CostructuredArrow.map f`. -/
@[stacks 002K "left Kan extension structure map in colimit coordinates"]
theorem objIsoColimit.map [L.HasPointwiseLeftKanExtension F]
    {X Y : D} (f : X ⟶ Y) :
    (L.leftKanExtensionObjIsoColimit F X).inv ≫
          (L.leftKanExtension F).map f ≫
        (L.leftKanExtensionObjIsoColimit F Y).hom =
      colimitMap L F f := sorry

/-- A colimit injection followed by the structure map of the chosen left Kan extension is the
injection obtained by postcomposing its indexing arrow. -/
@[stacks 002K "left Kan extension structure map on colimit injections"]
theorem objIsoColimit.ι_map [L.HasPointwiseLeftKanExtension F]
    {X Y : D} (f : X ⟶ Y) (g : CostructuredArrow L X) :
    colimit.ι (CostructuredArrow.proj L X ⋙ F) g ≫
          (L.leftKanExtensionObjIsoColimit F X).inv ≫
          (L.leftKanExtension F).map f ≫
        (L.leftKanExtensionObjIsoColimit F Y).hom =
      colimit.ι (CostructuredArrow.proj L Y ⋙ F)
        ((CostructuredArrow.map f).obj g) := sorry

end CategoryTheory.Functor.LeftKanExtension
