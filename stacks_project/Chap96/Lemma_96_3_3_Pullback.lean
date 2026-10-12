/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso

/-!
# Presheaf inverse-image isomorphisms from total-functor isomorphisms

A natural isomorphism of functors induces an isomorphism of the corresponding
presheaf inverse-image functors by opposite whiskering. A 2-morphism of
categories fibred in groupoids specializes this to `t^p`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v u' v' w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- The isomorphism of `A`-valued presheaf inverse images induced by a natural
isomorphism of covariant functors. If `e : F ≅ G`, then this is
`presheafInverseImage G A ≅ presheafInverseImage F A`. -/
def presheafInverseImageIso {F G : C ⥤ D} (e : F ≅ G) (A : Type w) [Category A] :
    presheafInverseImage G A ≅ presheafInverseImage F A :=
  (whiskeringLeft Cᵒᵖ Dᵒᵖ A).mapIso (NatIso.op e)

/-- The component of `presheafInverseImageIso e A` at a presheaf `𝒢` and an
object `x` is `𝒢.map (e.hom.app x).op`. -/
theorem presheafInverseImageIso_hom_app {F G : C ⥤ D} (e : F ≅ G)
    (A : Type w) [Category A] (𝒢 : Dᵒᵖ ⥤ A) (x : C) :
    ((presheafInverseImageIso e A).hom.app 𝒢).app (op x) =
      𝒢.map (e.hom.app x).op :=
  sorry

/-- The inverse-image isomorphism assigned to an identity natural isomorphism is
the identity. -/
theorem presheafInverseImageIso_refl (F : C ⥤ D) (A : Type w) [Category A] :
    presheafInverseImageIso (Iso.refl F) A = Iso.refl (presheafInverseImage F A) :=
  sorry

/-- Opposite whiskering reverses the order of composition of natural
isomorphisms. -/
theorem presheafInverseImageIso_trans {F G H : C ⥤ D} (e : F ≅ G) (d : G ≅ H)
    (A : Type w) [Category A] :
    presheafInverseImageIso (e ≪≫ d) A =
      presheafInverseImageIso d A ≪≫ presheafInverseImageIso e A :=
  sorry

end CategoryTheory.Functor

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

/-- Source component formula: on a presheaf `𝒢` the map `t^p` is the family
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
