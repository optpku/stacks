/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_15_1_Site
public import stacks_project.Chap85.Lemma_85_15_1
public import ReasLib.CategoryTheory.Sites.Family.Topos

/-!
# Localization morphism at a semi-representable object

The continuous and cocontinuous localization functor `forget K : OverSite K ⥤ C`
induces a morphism of topoi `Sh(C / K) ⟶ Sh(C)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

/- The morphism of topoi `Sh(C / K) ⟶ Sh(C)` induced by the continuous and
cocontinuous localization functor `forget K : OverSite K ⥤ C`. -/
#check (CategoryTheory.SemiRepresentableFamily.localizationMorphism :
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (K : FormalCoproduct.{w} C)
    [HasSheafify (overTopology J K) (Type (max w u v))]
    [∀ P : (OverSite K)ᵒᵖ ⥤ Type (max w u v),
      (forget K).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn J (overTopology J K))

end CategoryTheory.SemiRepresentableFamily
