/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_5_1_Comparison

/-!
# Base change for pushforward of presheaves on categories fibred in groupoids

A 2-cartesian square of categories fibred in groupoids over a scheme `S` yields a
canonical isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹` of Type-valued presheaf functors,
functorial in the presheaf on `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids (toFunctor total)
open scoped Bicategory

universe u w

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

noncomputable section

/-- Lemma 96.5.1: Let `S` be a scheme, and let
`f : X ⟶ Y` and `g : Y' ⟶ Y` be 1-morphisms of categories fibred in groupoids
over `(Sch/S)_fppf`. Write `X' = TwoFibreProduct.apex g f`, `f' = TwoFibreProduct.fst g f`,
and `g' = TwoFibreProduct.snd g f` for the chosen 2-cartesian square. Then there is a
canonical isomorphism `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of Type-valued presheaf functors,
functorial in the presheaf `F` on `X`. -/
@[stacks 075B]
def presheafBaseChangeIso {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F] :
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ⋙
        presheafInverseImage (toFunctor g) (Type w) ≅
      presheafInverseImage
          (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f)) (Type w) ⋙
        ((toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op.ran :
          ((total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w) ⥤
            (Y'.totalᵒᵖ ⥤ Type w)) :=
  FiberedCategoryOver.Groupoids.presheafBaseChangeIso f g

/-- The source-facing isomorphism is the 2-fibre-product mate comparison. -/
theorem presheafBaseChangeIso_eq {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      HasRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F] :
    presheafBaseChangeIso f g =
      FiberedCategoryOver.Groupoids.presheafBaseChangeIso f g :=
  sorry

end

end AlgebraicGeometry
