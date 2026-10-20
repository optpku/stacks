module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Presheaf.Pullback
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.RightKanBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Presheaf base change for categories fibred in groupoids

The inverse-image square of a two-fibre product has a canonical mate. When the
pushforwards exist pointwise, the mate is a natural isomorphism, with inverse
given by transport of compatible sections along the pseudo-pullback projections.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v uT vT w

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y Y' : Groupoids.{u, v, max uT (max u (max v vT)), max v vT} C}

noncomputable section

/-- The inverse-image 2-cell of the chosen 2-fibre product of `g` and `f`:
`g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`, obtained from `presheafInverseImage_compIso` and
`toFunctorIso` of `TwoFibreProduct.comparisonIso g f`. Here `f' = TwoFibreProduct.fst g f`
and `g' = TwoFibreProduct.snd g f`. -/
def presheafInverseImage_twoFibreIso (f : X ⟶ Y) (g : Y' ⟶ Y) :
    Functor.presheafInverseImage (toFunctor g) (Type w) ⋙
      Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)) (Type w) ≅
    Functor.presheafInverseImage (toFunctor f) (Type w) ⋙
      Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.snd.{u, v, uT, vT} g f)) (Type w) :=
  (presheafInverseImage_compIso (TwoFibreProduct.fst.{u, v, uT, vT} g f) g
      (Type w)).symm ≪≫
    Functor.presheafInverseImageIso
      (toFunctorIso (TwoFibreProduct.comparisonIso.{u, v, uT, vT} g f).symm)
      (Type w) ≪≫
    presheafInverseImage_compIso (TwoFibreProduct.snd.{u, v, uT, vT} g f) f
      (Type w)

/-- The canonical comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of Type-valued presheaf functors,
the mate of `presheafInverseImage_twoFibreIso` along the two `ranAdjunction`s. -/
def presheafBaseChangeHom (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F] :
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ⋙
        Functor.presheafInverseImage (toFunctor g) (Type w) ⟶
      Functor.presheafInverseImage
          (toFunctor (TwoFibreProduct.snd.{u, v, uT, vT} g f)) (Type w) ⋙
        ((toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op.ran :
          ((total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w) ⥤
            (Y'.totalᵒᵖ ⥤ Type w)) :=
  mateEquiv
    ((toFunctor f).op.ranAdjunction (Type w))
    ((toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op.ranAdjunction (Type w))
    (presheafInverseImage_twoFibreIso f g).hom

section ExplicitInverse

-- These private definitions must be usable in the body of the public isomorphism.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Pass the Kan-existence family explicitly across the definitionally equal apex and projection.
private theorem presheafBaseChangeInv_naturality (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [hfst : ∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F]
    {P Q : X.totalᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    (Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.snd.{u, v, uT, vT} g f)) (Type w) ⋙
      (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op.ran).map α ≫
        (@BasedCategory.PseudoPullback.RightKanBaseChange.presheafIso _ _ _ _ _
          (toBasedFunctor g) (toBasedFunctor f) inferInstance inferInstance
          (Type w) inferInstance Q inferInstance hfst).inv =
      (@BasedCategory.PseudoPullback.RightKanBaseChange.presheafIso _ _ _ _ _
          (toBasedFunctor g) (toBasedFunctor f) inferInstance inferInstance
          (Type w) inferInstance P inferInstance hfst).inv ≫
        ((toFunctor f).op.ran ⋙
          Functor.presheafInverseImage (toFunctor g) (Type w)).map α :=
  sorry

private def presheafBaseChangeInv (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [hfst : ∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F] :
    Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.snd.{u, v, uT, vT} g f)) (Type w) ⋙
      ((toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op.ran :
        ((total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w) ⥤
          (Y'.totalᵒᵖ ⥤ Type w)) ⟶
      ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ⋙
        Functor.presheafInverseImage (toFunctor g) (Type w) where
  app P := (@BasedCategory.PseudoPullback.RightKanBaseChange.presheafIso _ _ _ _ _
    (toBasedFunctor g) (toBasedFunctor f) inferInstance inferInstance
    (Type w) inferInstance P inferInstance hfst).inv
  naturality _ _ α := presheafBaseChangeInv_naturality f g α

private theorem presheafBaseChangeHom_inv_id (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F] :
    presheafBaseChangeHom f g ≫ presheafBaseChangeInv f g = 𝟙 _ :=
  sorry

private theorem presheafBaseChangeInv_hom_id (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F] :
    presheafBaseChangeInv f g ≫ presheafBaseChangeHom f g = 𝟙 _ :=
  sorry

/-- For a two-fibre product of categories fibred in groupoids, the canonical mate
is an isomorphism of presheaf functors whenever the two pushforwards exist pointwise. -/
def presheafBaseChangeIso (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F] :
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ⋙
        Functor.presheafInverseImage (toFunctor g) (Type w) ≅
      Functor.presheafInverseImage
          (toFunctor (TwoFibreProduct.snd.{u, v, uT, vT} g f)) (Type w) ⋙
        ((toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op.ran :
          ((total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w) ⥤
            (Y'.totalᵒᵖ ⥤ Type w)) where
  hom := presheafBaseChangeHom f g
  inv := presheafBaseChangeInv f g
  hom_inv_id := presheafBaseChangeHom_inv_id f g
  inv_hom_id := presheafBaseChangeInv_hom_id f g

end ExplicitInverse

/-- The base-change mate for a two-fibre product is invertible when both
pushforwards exist pointwise. -/
instance presheafBaseChangeHom.isIso (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F] :
    IsIso (presheafBaseChangeHom f g) :=
  (presheafBaseChangeIso f g).isIso_hom

/-- At each presheaf, the forward base-change isomorphism is the component of
the canonical mate of the inverse-image square. -/
theorem presheafBaseChangeIso_app (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u, v, uT, vT} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)).op F]
    (F : X.totalᵒᵖ ⥤ Type w) :
    (presheafBaseChangeIso f g).hom.app F = (presheafBaseChangeHom f g).app F :=
  rfl

end

end CategoryTheory.FiberedCategoryOver.Groupoids
