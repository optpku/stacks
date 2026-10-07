module

public import ReasLib.CategoryTheory.Sites.HigherDirectImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of higher direct images

This leaf owns the local criterion ensuring that a higher direct image commutes with a colimit.
The conclusion is stated for the canonical `colimit.post` morphism, so downstream results can
reuse the map rather than only an object-level isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v i j

namespace CategoryTheory.Sheaf.HigherDirectImage

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {I : Type i} [Category.{j} I]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [Functor.IsContinuous u JD JC]
variable [HasSheafify JC AddCommGrpCat.{v}] [HasSheafify JD AddCommGrpCat.{v}]
variable [HasExt (Sheaf JC AddCommGrpCat.{v})]
variable [HasInjectiveResolutions (Sheaf JC AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Sheaf JC AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Sheaf JD AddCommGrpCat.{v})]

/-- Lemma 21.16.4 (0H7B): if every object of the target site has a covering on
which the canonical cohomology-presheaf colimit comparison is invertible, then the canonical
colimit comparison for the degree-`p` higher direct image is invertible. -/
@[stacks 0H7B]
theorem colimitComparison_isIso_of_cover
    (F : I ⥤ Sheaf JC AddCommGrpCat.{v}) (p : ℕ)
    (hcover : ∀ V : D,
      ∃ S : JD.Cover V,
        ∀ A : S.Arrow,
          IsIso ((colimit.post F (cohomologyPresheafFunctor JC p)).app
            (op (u.obj A.Y)))) :
    IsIso (colimit.post F
      (@higherDirectImageFunctor C _ D _ JC JD u _ _ _ _ p)) := sorry

end CategoryTheory.Sheaf.HigherDirectImage
