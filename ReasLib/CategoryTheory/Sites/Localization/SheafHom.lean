/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.Basic
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Sheaf-Hom and slice localization

This leaf records the representable sheaf-Hom description of the direct image
of restriction to a slice site.  It is a proposition-level result, so it does
not need to choose an inverse for a representable-localization comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

noncomputable section

namespace CategoryTheory.Sheaf.HomRepresentable

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} (U : C)
variable [HasWeakSheafify J (Type (max u v))]
variable [HasSheafify (J.over U) (Type (max u v))]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v),
  (Over.forget U).op.HasPointwiseRightKanExtension P]

/-- The sheaf-Hom from the sheafified representable of `U` to `F` is isomorphic to the direct
image of the restriction of `F` along localization at `U`. -/
theorem isomorphic_pushforwardRestriction (F : Sheaf J (Type (max u v))) :
    IsIsomorphic
      (sheafHom (J.sheafifiedRepresentable U) F)
      ((J.localizationMorphism U).pushforward.obj (F.over U)) := sorry

end CategoryTheory.Sheaf.HomRepresentable
