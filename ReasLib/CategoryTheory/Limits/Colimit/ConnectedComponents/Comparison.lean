module

public import ReasLib.CategoryTheory.Limits.Colimit.ConnectedComponents.Basic

/-!
# Comparison for componentwise colimits

This module compares the coproduct of the connected-component colimits of an arbitrary diagram
on `J` with its chosen total colimit and records the comparison's computation and naturality API.
-/

@[expose] public section

open CategoryTheory

universe v u vJ uJ

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type u} [Category.{v} C]

/-- The colimit of a diagram is canonically isomorphic to the coproduct of its restrictions to
the connected components of the indexing category. -/
noncomputable def componentColimitIso
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    [HasColimit F] :
    (∐ fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F)) ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso
    (componentColimitCocone.isColimit F) (colimit.isColimit F)

namespace componentColimitIso

/-- The forward component-colimit comparison sends a component leg to the corresponding total
colimit leg. -/
@[reassoc (attr := simp)]
theorem ι_hom
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    [HasColimit F] (q : ConnectedComponents J) (X : q.Component) :
    colimit.ι (ConnectedComponents.ι q ⋙ F) X ≫
        Limits.Sigma.ι
          (fun r : ConnectedComponents J =>
            colimit (ConnectedComponents.ι r ⋙ F)) q ≫
      (componentColimitIso F).hom =
        colimit.ι F ((ConnectedComponents.ι q).obj X) := sorry

/-- The inverse component-colimit comparison sends a total colimit leg to the corresponding
component leg followed by the coproduct injection. -/
@[reassoc (attr := simp)]
theorem ι_inv
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    [HasColimit F] (q : ConnectedComponents J) (X : q.Component) :
    colimit.ι F ((ConnectedComponents.ι q).obj X) ≫ (componentColimitIso F).inv =
      colimit.ι (ConnectedComponents.ι q ⋙ F) X ≫
        Limits.Sigma.ι
          (fun r : ConnectedComponents J =>
            colimit (ConnectedComponents.ι r ⋙ F)) q := sorry

/-- Under the component-colimit comparisons, the map on total colimits is the coproduct of the
maps on componentwise colimits. -/
theorem colimMap
    {F G : J ⥤ C} (α : F ⟶ G)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ G)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ G))]
    [HasColimit F] [HasColimit G] :
    Limits.colimMap α =
      (componentColimitIso F).inv ≫
        Limits.Sigma.map
          (fun q : ConnectedComponents J =>
            Limits.colimMap (Functor.whiskerLeft (ConnectedComponents.ι q) α)) ≫
        (componentColimitIso G).hom := sorry

/-- Naturality of the forward component-colimit comparison. -/
@[reassoc]
theorem hom_naturality
    {F G : J ⥤ C} (α : F ⟶ G)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ G)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ G))]
    [HasColimit F] [HasColimit G] :
    Limits.Sigma.map
        (fun q : ConnectedComponents J =>
          Limits.colimMap (Functor.whiskerLeft (ConnectedComponents.ι q) α)) ≫
      (componentColimitIso G).hom =
        (componentColimitIso F).hom ≫ Limits.colimMap α := sorry

/-- Naturality of the inverse component-colimit comparison. -/
@[reassoc]
theorem inv_naturality
    {F G : J ⥤ C} (α : F ⟶ G)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ G)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ G))]
    [HasColimit F] [HasColimit G] :
    Limits.colimMap α ≫ (componentColimitIso G).inv =
      (componentColimitIso F).inv ≫
        Limits.Sigma.map
          (fun q : ConnectedComponents J =>
            Limits.colimMap (Functor.whiskerLeft (ConnectedComponents.ι q) α)) := sorry

end componentColimitIso

end CategoryTheory.Limits
