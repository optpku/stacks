/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.SheafHom
import StacksCheckRecall

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

open CategoryTheory.SemiRepresentableFamily

/- Lemma 85.15.2: Let `C` be a site and `K` in `SR(C)`. For `F` in `Sh(C)` we have
`j_* (j⁻¹ F) = sheafHom (F(K)^#) F`, where `j : C / K ⥤ C` is localization at `K`
and `F(K)^#` is the sheafification of `FormalCoproduct.toPresheaf.obj K`, identified
in `Sh(C)` with `sheafifiedRepresentableCoproduct` because sheafification preserves
coproducts. -/
@[stacks 0D86] #check
  (CategoryTheory.Sheaf.HomRepresentable.isomorphic_pushforwardInverseImage :
    ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
      (K : FormalCoproduct.{w} C)
      [HasWeakSheafify J (Type (max w u v))]
      [HasSheafify (overTopology J K) (Type (max w u v))]
      [∀ P : (OverSite K)ᵒᵖ ⥤ Type (max w u v),
        (SemiRepresentableFamily.forget K).op.HasPointwiseRightKanExtension P]
      (F : Sheaf J (Type (max w u v))),
    IsIsomorphic
      ((localizationMorphism J K).pushforward.obj
        ((localizationMorphism J K).inverseImage.obj F))
      (sheafHom (J.sheafifiedRepresentableCoproduct K) F))
