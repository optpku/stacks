module

public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImageIso
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso

/-!
# Presheaf pullback isomorphisms for categories fibred in groupoids

A 2-morphism induces a contravariant isomorphism of presheaf inverse images,
compatible with identities, vertical composition, and bicategorical whiskering.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v u' v' w

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open scoped Bicategory
open ObjectProperty

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

noncomputable section

/-- The presheaf inverse-image isomorphism `t^p : g^p ≅ f^p` assigned to a
2-morphism `t : f ⟶ g` of categories fibred in groupoids. -/
def presheafInverseImageIso {f g : X ⟶ Y} (t : f ⟶ g) :
    Functor.presheafInverseImage (toFunctor g) (Type w) ≅
      Functor.presheafInverseImage (toFunctor f) (Type w) :=
  Functor.presheafInverseImageIso (toFunctorIso (asIso t)) (Type w)

/-- On a presheaf `𝒢`, the inverse-image isomorphism is the family
`𝒢.map ((toNatTrans t).app x).op`. -/
theorem presheafInverseImageIso_hom_app {f g : X ⟶ Y} (t : f ⟶ g)
    (𝒢 : Y.totalᵒᵖ ⥤ Type w) (x : X.total) :
    ((presheafInverseImageIso t).hom.app 𝒢).app (op x) =
      𝒢.map ((toNatTrans t).app x).op :=
  sorry

/-- The inverse-image isomorphism assigned to an identity 2-morphism is the
identity. -/
theorem presheafInverseImageIso_id {f : X ⟶ Y} :
    presheafInverseImageIso (𝟙 f) =
      Iso.refl (Functor.presheafInverseImage (toFunctor f) (Type w)) :=
  sorry

/-- Vertical composition of 2-morphisms is reversed by `t^p`. -/
theorem presheafInverseImageIso_comp {f g h : X ⟶ Y} (t : f ⟶ g) (s : g ⟶ h) :
    presheafInverseImageIso (t ≫ s) =
      presheafInverseImageIso s ≪≫ presheafInverseImageIso t :=
  sorry

/-- Comparison of inverse image along a composite 1-morphism with inverse image
along the composite of the underlying total functors. -/
def presheafInverseImage_compIso {Z : FiberedCategoryOver.Groupoids C}
    (f : X ⟶ Y) (h : Y ⟶ Z) (A : Type w) [Category A] :
    Functor.presheafInverseImage (toFunctor (f ≫ h)) A ≅
      Functor.presheafInverseImage (toFunctor f ⋙ toFunctor h) A :=
  Functor.presheafInverseImageIso (FullSubbicategory.toFunctor.compIso f h) A

/-- Left Bicategory whiskering of a 2-morphism is compatible with `t^p` after
the total-functor composition comparison. -/
theorem presheafInverseImageIso_whiskerLeft {Z : FiberedCategoryOver.Groupoids C}
    (f : X ⟶ Y) {h k : Y ⟶ Z} (s : h ⟶ k) :
    presheafInverseImageIso (f ◁ s) =
      presheafInverseImage_compIso f k (Type w) ≪≫
        Functor.isoWhiskerRight (presheafInverseImageIso s)
          (Functor.presheafInverseImage (toFunctor f) (Type w)) ≪≫
        (presheafInverseImage_compIso f h (Type w)).symm :=
  sorry

/-- Right Bicategory whiskering of a 2-morphism is compatible with `t^p` after
the total-functor composition comparison. -/
theorem presheafInverseImageIso_whiskerRight {Z : FiberedCategoryOver.Groupoids C}
    {f g : X ⟶ Y} (t : f ⟶ g) (h : Y ⟶ Z) :
    presheafInverseImageIso (t ▷ h) =
      presheafInverseImage_compIso g h (Type w) ≪≫
        Functor.isoWhiskerLeft (Functor.presheafInverseImage (toFunctor h) (Type w))
          (presheafInverseImageIso t) ≪≫
        (presheafInverseImage_compIso f h (Type w)).symm :=
  sorry

end

end CategoryTheory.FiberedCategoryOver.Groupoids
