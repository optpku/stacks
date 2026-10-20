module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Construction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Images of Telescope Presentations

This file defines the cocone obtained by applying a functor to a telescope
presentation and its canonical colimit comparison.  The comparison requests
only a colimit of the particular image diagram.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory.HomotopyColimit.Presentation

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A]
variable {K : ℕ ⥤ D} {X : D}

/-- The cocone obtained by applying a functor to the cocone of a telescope presentation. -/
@[stacks 0CRK]
def imageCocone (P : Presentation K X) (H : D ⥤ A) : Cocone (K ⋙ H) :=
  H.mapCocone P.cocone

/-- The point of the image cocone is the image of the presented object. -/
@[simp]
theorem imageCocone_pt (P : Presentation K X) (H : D ⥤ A) :
    (imageCocone P H).pt = H.obj X := sorry

/-- The `n`th image-cocone leg is the image of the `n`th presentation leg. -/
@[simp, reassoc]
theorem imageCocone_ι_app (P : Presentation K X) (H : D ⥤ A) (n : ℕ) :
    (imageCocone P H).ι.app n = H.map (P.ι n) := sorry

/-- The canonical comparison from the colimit of an image diagram to the image of the
presented object. -/
@[stacks 0CRK]
noncomputable def imageComparison (P : Presentation K X) (H : D ⥤ A)
    [HasColimit (K ⋙ H)] :
    colimit (K ⋙ H) ⟶ H.obj X :=
  colimit.desc _ (imageCocone P H)

/-- The image comparison restricts on each colimit leg to the corresponding image
presentation leg. -/
@[simp, reassoc]
theorem colimit_ι_comp_imageComparison (P : Presentation K X) (H : D ⥤ A)
    [HasColimit (K ⋙ H)] (n : ℕ) :
    colimit.ι (K ⋙ H) n ≫ imageComparison P H = H.map (P.ι n) := sorry

end CategoryTheory.HomotopyColimit.Presentation

end
