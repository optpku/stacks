module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.CategoryTheory.ConnectedComponents

/-!
# The connected-component colimit cocone

An arbitrary diagram on `J` has a canonical cocone whose point is the coproduct of the colimits
of its restrictions to the connected components of `J`.
-/

@[expose] public section

open CategoryTheory

universe v u vJ uJ

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type u} [Category.{v} C]

namespace componentColimitCocone

/-- The legs from a diagram to the coproduct of its componentwise colimits are natural in the
original index. -/
theorem naturality
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    {X Y : J} (f : X ⟶ Y) :
    F.map f ≫
        colimit.ι (ConnectedComponents.ι (ConnectedComponents.mk Y) ⋙ F) ⟨Y, rfl⟩ ≫
        Limits.Sigma.ι
          (fun q : ConnectedComponents J =>
            colimit (ConnectedComponents.ι q ⋙ F)) (ConnectedComponents.mk Y) =
      (colimit.ι (ConnectedComponents.ι (ConnectedComponents.mk X) ⋙ F) ⟨X, rfl⟩ ≫
        Limits.Sigma.ι
          (fun q : ConnectedComponents J =>
            colimit (ConnectedComponents.ι q ⋙ F)) (ConnectedComponents.mk X)) ≫
        ((Functor.const J).obj
          (∐ fun q : ConnectedComponents J =>
            colimit (ConnectedComponents.ι q ⋙ F))).map f := sorry

end componentColimitCocone

/-- The canonical cocone from a diagram to the coproduct of its componentwise colimits. -/
noncomputable def componentColimitCocone
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))] :
    Cocone F where
  pt := ∐ fun q : ConnectedComponents J => colimit (ConnectedComponents.ι q ⋙ F)
  ι :=
    { app := fun X =>
        colimit.ι (ConnectedComponents.ι (ConnectedComponents.mk X) ⋙ F) ⟨X, rfl⟩ ≫
          Limits.Sigma.ι
            (fun q : ConnectedComponents J =>
              colimit (ConnectedComponents.ι q ⋙ F)) (ConnectedComponents.mk X)
      naturality := fun _ _ f => componentColimitCocone.naturality F f }

namespace componentColimitCocone

/-- The universal morphism from the componentwise cocone to another cocone, obtained by first
descending from each component colimit and then from their coproduct. -/
noncomputable def desc
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    (s : Cocone F) : (componentColimitCocone F).pt ⟶ s.pt :=
  Limits.Sigma.desc
    (fun q : ConnectedComponents J =>
      colimit.desc (ConnectedComponents.ι q ⋙ F)
        (Cocone.whisker (ConnectedComponents.ι q) s))

/-- The universal morphism from the componentwise cocone factors every cocone leg. -/
theorem fac
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    (s : Cocone F) (X : J) :
    (componentColimitCocone F).ι.app X ≫ desc F s = s.ι.app X := sorry

/-- A morphism from the componentwise cocone point is determined by its composites with all
cocone legs. -/
theorem uniq
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))]
    (s : Cocone F) (m : (componentColimitCocone F).pt ⟶ s.pt)
    (h : ∀ X, (componentColimitCocone F).ι.app X ≫ m = s.ι.app X) :
    m = desc F s := sorry

/-- The canonical componentwise cocone is a colimit cocone. Its universal morphism is
`componentColimitCocone.desc`. -/
noncomputable def isColimit
    (F : J ⥤ C)
    [∀ q : ConnectedComponents J, HasColimit (ConnectedComponents.ι q ⋙ F)]
    [HasCoproduct (fun q : ConnectedComponents J =>
      colimit (ConnectedComponents.ι q ⋙ F))] :
    IsColimit (componentColimitCocone F) where
  desc := desc F
  fac := fac F
  uniq := uniq F

end componentColimitCocone

end CategoryTheory.Limits
