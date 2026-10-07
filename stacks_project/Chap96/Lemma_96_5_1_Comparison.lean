module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import stacks_project.Chap96.Lemma_96_3_3_Pullback

/-!
# Presheaf base-change comparison on a 2-fibre product

For a cospan of categories fibred in groupoids over `(Sch/S)_fppf`, the chosen
2-fibre product supplies an isomorphism of inverse-image composites. Its mate
along the two right Kan-extension adjunctions is the comparison
`g⁻¹ ∘ f_* ⟶ f'_* ∘ (g')⁻¹` of Type-valued presheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u w

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {S : Scheme.{u}}
variable {X Y Y' : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}

noncomputable section

/-- The inverse-image 2-cell of the chosen 2-fibre product of `g` and `f`:
`g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`, obtained from `presheafInverseImage_compIso` and
`toFunctorIso` of `TwoFibreProduct.comparisonIso g f`. Here `f' = TwoFibreProduct.fst g f`
and `g' = TwoFibreProduct.snd g f`. -/
def presheafInverseImage_twoFibreIso (f : X ⟶ Y) (g : Y' ⟶ Y) :
    Functor.presheafInverseImage (toFunctor g) (Type w) ⋙
      Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)) (Type w) ≅
    Functor.presheafInverseImage (toFunctor f) (Type w) ⋙
      Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f)) (Type w) :=
  (presheafInverseImage_compIso (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) g
      (Type w)).symm ≪≫
    Functor.presheafInverseImageIso
      (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f).symm)
      (Type w) ≪≫
    presheafInverseImage_compIso (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f) f
      (Type w)

/-- The canonical comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of Type-valued presheaf functors,
the mate of `presheafInverseImage_twoFibreIso` along the two `ranAdjunction`s. -/
def presheafBaseChangeHom (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F] :
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ⋙
        Functor.presheafInverseImage (toFunctor g) (Type w) ⟶
      Functor.presheafInverseImage
          (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f)) (Type w) ⋙
        ((toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op.ran :
          ((total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w) ⥤
            (Y'.totalᵒᵖ ⥤ Type w)) :=
  mateEquiv
    ((toFunctor f).op.ranAdjunction (Type w))
    ((toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op.ranAdjunction (Type w))
    (presheafInverseImage_twoFibreIso f g).hom

/-- The comparison of a 2-fibre product of categories fibred in groupoids is invertible,
by the fibre-product identification of pushforwards. -/
instance presheafBaseChangeHom.isIso (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F] :
    IsIso (presheafBaseChangeHom f g) :=
  sorry

/-- The canonical isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of Type-valued presheaf functors
on the chosen 2-fibre product of `g` and `f`. -/
def presheafBaseChangeIso (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F] :
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ⋙
        Functor.presheafInverseImage (toFunctor g) (Type w) ≅
      Functor.presheafInverseImage
          (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f)) (Type w) ⋙
        ((toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op.ran :
          ((total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w) ⥤
            (Y'.totalᵒᵖ ⥤ Type w)) :=
  asIso (presheafBaseChangeHom f g)

/-- `presheafBaseChangeIso` is `asIso` of the mate comparison. -/
theorem presheafBaseChangeIso_eq (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F] :
    presheafBaseChangeIso f g = asIso (presheafBaseChangeHom f g) :=
  sorry

/-- At a presheaf `F` on `X`, the comparison is the component of the mate. -/
theorem presheafBaseChangeIso_app (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      Functor.HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F]
    (F : X.totalᵒᵖ ⥤ Type w) :
    (presheafBaseChangeIso f g).hom.app F = (presheafBaseChangeHom f g).app F :=
  sorry

end

end CategoryTheory.FiberedCategoryOver.Groupoids
