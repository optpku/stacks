module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap63.«63_4_0_2_LowerShriekPresheaf»

/-!
# Direct image with compact support for locally quasi-finite morphisms

The abelian functor `f_!` is the sheafification of the compact-support
presheaf `f_{p!}`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The direct image with compact support `f_!` along a locally quasi-finite
morphism, obtained by sheafifying the presheaf `f_{p!}`. -/
def lowerShriek :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  lowerShriekPresheaf f ⋙ presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}

/-- Evaluating `f_!` sheafifies the compact-support presheaf `f_{p!}`. -/
theorem lowerShriek_obj (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f).obj F =
      (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((lowerShriekPresheaf f).obj F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
