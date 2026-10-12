/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafHom
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Coproduct
public import stacks_project.Chap85.Lemma_85_15_2_Localization

/-!
# Lemma 85.15.2

Push-pull of a sheaf along localization at a semi-representable object is internal
Hom out of the sheafified coproduct of representables.
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

/-- Lemma 85.15.2: Let `C` be a site and `K` in `SR(C)`. For `F` in `Sh(C)` we have
`j_* (j⁻¹ F) = sheafHom (F(K)^#) F`, where `j : C / K ⥤ C` is localization at `K`
and `F(K)^#` is the sheafification of `FormalCoproduct.toPresheaf.obj K`, identified
in `Sh(C)` with `sheafifiedRepresentableCoproduct` because sheafification preserves
coproducts. -/
@[stacks 0D86]
theorem isomorphic_pushforwardInverseImage (F : Sheaf J (Type (max w u v))) :
    IsIsomorphic
      ((localizationMorphism J K).pushforward.obj
        ((localizationMorphism J K).inverseImage.obj F))
      (sheafHom (J.sheafifiedRepresentableCoproduct K) F) := sorry

end CategoryTheory.Sheaf.HomRepresentable
