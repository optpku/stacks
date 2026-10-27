/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits CategoricalPullback

/-!
# Mapping-path categories

For a functor `F : C ⥤ D`, `Functor.MappingPath F` is the categorical pullback
`(𝟭 D) ⊡ F`.  The first projection is a standard isofibration replacement of `F`, while the
canonical inclusion of `C` is an equivalence.  This is ordinary-category infrastructure, kept
independent of the bicategorical applications that use it.
-/

namespace Functor

section MappingPath

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]

/-- The mapping-path category of F : C ⥤ D is the iso-comma category of 𝟭 D and F.
Its objects are triples (d, c, e : d ≅ F.obj c). -/
abbrev MappingPath (F : C ⥤ D) :=
  (𝟭 D) ⊡ F

namespace MappingPath

/-- The first projection from the mapping-path category. This remains an abbrev because it is the
frequent transparent projection view of the canonical CategoricalPullback owner. -/
abbrev projection (F : C ⥤ D) : Functor.MappingPath F ⥤ D :=
  π₁ (𝟭 D) F

section InclusionImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The canonical mapping-path object associated to an object of the source. -/
private def inclusionObj (F : C ⥤ D) (X : C) : Functor.MappingPath F where
  fst := F.obj X
  snd := X
  iso := Iso.refl _

/-- Compatibility of the two components of a canonical mapping-path morphism.

Proof strategy: unfold inclusionObj; both structural isomorphisms are identities, so the claim is
the identity-functor map equation followed by the category identity laws. -/
private theorem inclusionMap_w (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (𝟭 D).map (F.map f) ≫ (inclusionObj F Y).iso.hom =
      (inclusionObj F X).iso.hom ≫ F.map f := by
  simp [inclusionObj]

/-- The canonical mapping-path morphism associated to a source morphism. -/
private def inclusionMap (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    inclusionObj F X ⟶ inclusionObj F Y where
  fst := F.map f
  snd := f
  w := inclusionMap_w F f

/-- The canonical mapping-path map preserves identities.

Proof strategy: apply CategoricalPullback.hom_ext and use F.map_id on the first component and the
category identity law on the second component. -/
private theorem inclusionMap_id (F : C ⥤ D) (X : C) :
    inclusionMap F (𝟙 X) = 𝟙 (inclusionObj F X) := by
  apply CategoricalPullback.hom_ext
  · change F.map (𝟙 X) = 𝟙 (F.obj X)
    exact F.map_id X
  · rfl

/-- The canonical mapping-path map preserves composition.

Proof strategy: apply CategoricalPullback.hom_ext; the first component is F.map_comp and the
second component is definitionally the original composite. -/
private theorem inclusionMap_comp (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    inclusionMap F (f ≫ g) = inclusionMap F f ≫ inclusionMap F g := by
  apply CategoricalPullback.hom_ext
  · change F.map (f ≫ g) = F.map f ≫ F.map g
    exact F.map_comp f g
  · rfl

end Implementation

/-- The canonical inclusion of a category into the mapping path of a functor. -/
def inclusion (F : C ⥤ D) : C ⥤ Functor.MappingPath F where
  obj := Implementation.inclusionObj F
  map := Implementation.inclusionMap F
  map_id := Implementation.inclusionMap_id F
  map_comp := Implementation.inclusionMap_comp F

end InclusionImplementation

/-- The first component of a canonical mapping-path object.

Proof strategy: unfold inclusion and its private object implementation. -/
@[simp] theorem inclusion_obj_fst (F : C ⥤ D) (X : C) :
    ((inclusion F).obj X).fst = F.obj X := rfl

/-- The second component of a canonical mapping-path object.

Proof strategy: unfold inclusion and its private object implementation. -/
@[simp] theorem inclusion_obj_snd (F : C ⥤ D) (X : C) :
    ((inclusion F).obj X).snd = X := rfl

/-- The comparison isomorphism of a canonical mapping-path object.

Proof strategy: unfold inclusion and its private object implementation. -/
@[simp] theorem inclusion_obj_iso (F : C ⥤ D) (X : C) :
    ((inclusion F).obj X).iso = Iso.refl _ := rfl

/-- The first component of the canonical mapping-path image of a morphism.

Proof strategy: unfold inclusion and its private map implementation. -/
@[simp] theorem inclusion_map_fst (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    ((inclusion F).map f).fst = F.map f := rfl

/-- The second component of the canonical mapping-path image of a morphism.

Proof strategy: unfold inclusion and its private map implementation. -/
@[simp] theorem inclusion_map_snd (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    ((inclusion F).map f).snd = f := rfl

/-- The unit component of the mapping-path equivalence is the identity on the original source
object. -/
def inclusionUnitIsoApp (F : C ⥤ D) (X : C) :
    X ≅ ((inclusion F) ⋙ π₂ (𝟭 D) F).obj X :=
  Iso.refl X

/-- The identity unit components of the mapping-path equivalence are natural. -/
theorem inclusionUnitIsoApp_naturality
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    f ≫ (inclusionUnitIsoApp F Y).hom =
      (inclusionUnitIsoApp F X).hom ≫
        ((inclusion F) ⋙ π₂ (𝟭 D) F).map f := by
  change f ≫ 𝟙 Y = 𝟙 X ≫ f
  simp

/-- The unit of the canonical mapping-path equivalence. -/
def inclusionUnitIso (F : C ⥤ D) :
    𝟭 C ≅ (inclusion F) ⋙ π₂ (𝟭 D) F :=
  NatIso.ofComponents (inclusionUnitIsoApp F)
    (inclusionUnitIsoApp_naturality F)

/-- Compatibility of the two components of the mapping-path counit. -/
theorem inclusionCounitIsoApp_comm (F : C ⥤ D) (X : Functor.MappingPath F) :
    (𝟭 D).map X.iso.inv ≫ X.iso.hom =
      (Iso.refl (F.obj X.snd)).hom ≫
        F.map (Iso.refl X.snd).hom := by
  simp

/-- The counit component of the mapping-path equivalence uses the stored comparison isomorphism
on the first projection and the identity on the second projection. -/
def inclusionCounitIsoApp (F : C ⥤ D) (X : Functor.MappingPath F) :
    ((π₂ (𝟭 D) F) ⋙ inclusion F).obj X ≅ X :=
  CategoricalPullback.mkIso X.iso.symm (Iso.refl X.snd)
    (inclusionCounitIsoApp_comm F X)

/-- The explicit mapping-path counit components are natural. -/
theorem inclusionCounitIsoApp_naturality
    (F : C ⥤ D) {X Y : Functor.MappingPath F} (f : X ⟶ Y) :
    ((π₂ (𝟭 D) F) ⋙ inclusion F).map f ≫
        (inclusionCounitIsoApp F Y).hom =
      (inclusionCounitIsoApp F X).hom ≫ f := by
  apply CategoricalPullback.hom_ext
  · change F.map f.snd ≫ Y.iso.inv = X.iso.inv ≫ f.fst
    simpa using f.w'
  · change f.snd ≫ 𝟙 Y.snd = 𝟙 X.snd ≫ f.snd
    simp

/-- The counit of the canonical mapping-path equivalence. -/
def inclusionCounitIso (F : C ⥤ D) :
    (π₂ (𝟭 D) F) ⋙ inclusion F ≅ 𝟭 (Functor.MappingPath F) :=
  NatIso.ofComponents (inclusionCounitIsoApp F)
    (inclusionCounitIsoApp_naturality F)

/-- The explicit mapping-path unit and counit satisfy the equivalence triangle identity. -/
theorem inclusionEquivalence_triangle (F : C ⥤ D) (X : C) :
    (inclusion F).map ((inclusionUnitIso F).hom.app X) ≫
        (inclusionCounitIso F).hom.app ((inclusion F).obj X) =
      𝟙 ((inclusion F).obj X) := by
  apply CategoricalPullback.hom_ext
  · change F.map (𝟙 X) ≫ (Iso.refl (F.obj X)).inv = 𝟙 (F.obj X)
    simp
  · change 𝟙 X ≫ 𝟙 X = 𝟙 X
    simp

/-- The canonical equivalence from a category to the mapping path of a functor. Its inverse is
the second pullback projection, so no inverse-object choice is introduced. -/
def inclusionEquivalence (F : C ⥤ D) :
    C ≌ Functor.MappingPath F :=
  Equivalence.mk'
    (inclusion F)
    (π₂ (𝟭 D) F)
    (inclusionUnitIso F)
    (inclusionCounitIso F)
    (inclusionEquivalence_triangle F)

/-- The forward functor of the mapping-path equivalence is the canonical inclusion. -/
@[simp]
theorem inclusionEquivalence_functor (F : C ⥤ D) :
    (inclusionEquivalence F).functor = inclusion F := rfl

/-- The inverse functor of the mapping-path equivalence is the second pullback projection. -/
@[simp]
theorem inclusionEquivalence_inverse (F : C ⥤ D) :
    (inclusionEquivalence F).inverse = π₂ (𝟭 D) F := rfl

/-- The unit of the mapping-path equivalence is the named identity comparison. -/
@[simp]
theorem inclusionEquivalence_unitIso (F : C ⥤ D) :
    (inclusionEquivalence F).unitIso = inclusionUnitIso F := rfl

/-- The counit of the mapping-path equivalence is the named comparison built from each
mapping-path object's stored isomorphism. -/
@[simp]
theorem inclusionEquivalence_counitIso (F : C ⥤ D) :
    (inclusionEquivalence F).counitIso = inclusionCounitIso F := rfl

/-- The first component of the forward mapping-path counit is the inverse stored comparison
isomorphism. -/
@[simp]
theorem inclusionEquivalence_counitIso_hom_app_fst
    (F : C ⥤ D) (X : Functor.MappingPath F) :
    ((inclusionEquivalence F).counitIso.hom.app X).fst =
      X.iso.inv := rfl

/-- The second component of the forward mapping-path counit is the identity. -/
@[simp]
theorem inclusionEquivalence_counitIso_hom_app_snd
    (F : C ⥤ D) (X : Functor.MappingPath F) :
    ((inclusionEquivalence F).counitIso.hom.app X).snd =
      𝟙 X.snd := rfl

/-- The first component of the inverse mapping-path counit is the stored comparison
isomorphism. -/
@[simp]
theorem inclusionEquivalence_counitIso_inv_app_fst
    (F : C ⥤ D) (X : Functor.MappingPath F) :
    ((inclusionEquivalence F).counitIso.inv.app X).fst =
      X.iso.hom := rfl

/-- The second component of the inverse mapping-path counit is the identity. -/
@[simp]
theorem inclusionEquivalence_counitIso_inv_app_snd
    (F : C ⥤ D) (X : Functor.MappingPath F) :
    ((inclusionEquivalence F).counitIso.inv.app X).snd =
      𝟙 X.snd := rfl

/-- The canonical mapping-path inclusion is an equivalence.

Proof strategy: use the explicit `inclusionEquivalence F`, whose inverse is projection to the
second component. -/
instance inclusionIsEquivalence (F : C ⥤ D) :
    (inclusion F).IsEquivalence :=
  (inclusionEquivalence F).isEquivalence_functor

end MappingPath

end MappingPath

end Functor

end CategoryTheory
