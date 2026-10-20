module

public import ReasLib.CategoryTheory.Sites.Family.Topos
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Coproduct
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Internal Hom and family localization

Push-pull along family localization is internal Hom out of the corresponding
coproduct of sheafified representables.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SemiRepresentableFamily

universe w u v

noncomputable section

namespace CategoryTheory.Sheaf.HomRepresentable

open SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} (K : FormalCoproduct.{w} C)
variable [HasWeakSheafify J (Type (max w u v))]
variable [HasSheafify (overTopology J K) (Type (max w u v))]
variable [∀ P : (OverSite K)ᵒᵖ ⥤ Type (max w u v),
  (SemiRepresentableFamily.forget K).op.HasPointwiseRightKanExtension P]

/-- Push-pull of a sheaf along localization at an indexed family is isomorphic
to internal Hom from the coproduct of the family's sheafified representables
to that sheaf. -/
theorem isomorphic_pushforwardInverseImage (F : Sheaf J (Type (max w u v))) :
    IsIsomorphic
      ((localizationMorphism J K).pushforward.obj
        ((localizationMorphism J K).inverseImage.obj F))
      (sheafHom (J.sheafifiedRepresentableCoproduct K) F) := sorry

end CategoryTheory.Sheaf.HomRepresentable
