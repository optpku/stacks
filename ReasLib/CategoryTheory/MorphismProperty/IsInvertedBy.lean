module

public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Isomorphisms obtained from inverted morphisms

This leaf packages the canonical isomorphism obtained by applying a functor which inverts a
morphism property.  It is deliberately independent of localization constructions, so derived,
fibered, and bicategorical applications can share the same data owner.
-/

open CategoryTheory

noncomputable section

universe vC vD uC uD

namespace CategoryTheory.MorphismProperty.IsInvertedBy

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The canonical isomorphism `F.obj X ≅ F.obj Y` attached to `hF : W.IsInvertedBy F` and
`f : X ⟶ Y` with `W f`. -/
noncomputable def mapIso
    {W : MorphismProperty C} {F : C ⥤ D}
    (hF : W.IsInvertedBy F) {X Y : C} (f : X ⟶ Y) (hf : W f) : F.obj X ≅ F.obj Y :=
  @asIso _ _ _ _ (F.map f) (hF f hf)

/-- The hom of `mapIso` is the functorial image of the inverted morphism. -/
@[simp]
theorem mapIso_hom
    {W : MorphismProperty C} {F : C ⥤ D}
    (hF : W.IsInvertedBy F) {X Y : C} (f : X ⟶ Y) (hf : W f) :
    (mapIso hF f hf).hom = F.map f := sorry

/-- The inverse of `mapIso` is the inverse of the functorial image. -/
@[simp]
theorem mapIso_inv
    {W : MorphismProperty C} {F : C ⥤ D}
    (hF : W.IsInvertedBy F) {X Y : C} (f : X ⟶ Y) (hf : W f) :
    (mapIso hF f hf).inv =
      @CategoryTheory.inv _ _ _ _ (F.map f) (hF f hf) := sorry

/-- Transport an isomorphism `G ≅ F.obj X` across a morphism inverted by `F`. -/
noncomputable def transportIso
    {W : MorphismProperty C} {F : C ⥤ D}
    (hF : W.IsInvertedBy F) {X Y : C} (f : X ⟶ Y) (hf : W f)
    {G : D} (e : G ≅ F.obj X) : G ≅ F.obj Y :=
  e ≪≫ hF.mapIso f hf

/-- The forward map of `transportIso` is the displayed composite. -/
@[simp]
theorem transportIso_hom
    {W : MorphismProperty C} {F : C ⥤ D}
    (hF : W.IsInvertedBy F) {X Y : C} (f : X ⟶ Y) (hf : W f)
    {G : D} (e : G ≅ F.obj X) :
    (transportIso hF f hf e).hom = e.hom ≫ F.map f := sorry

/-- The inverse map of `transportIso` is the reverse composite. -/
@[simp]
theorem transportIso_inv
    {W : MorphismProperty C} {F : C ⥤ D}
    (hF : W.IsInvertedBy F) {X Y : C} (f : X ⟶ Y) (hf : W f)
    {G : D} (e : G ≅ F.obj X) :
    (transportIso hF f hf e).inv =
      @CategoryTheory.inv _ _ _ _ (F.map f) (hF f hf) ≫ e.inv := sorry

end CategoryTheory.MorphismProperty.IsInvertedBy
