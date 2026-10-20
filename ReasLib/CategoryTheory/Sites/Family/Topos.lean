/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Localization
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous

/-!
# Morphisms of topoi from family localization

Localization at an indexed family of objects induces a morphism of topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
variable [HasSheafify (overTopology J K) (Type (max w u v))]
variable [∀ P : (OverSite K)ᵒᵖ ⥤ Type (max w u v),
  (forget K).op.HasPointwiseRightKanExtension P]

/-- The morphism of topoi `Sh(C / K) ⟶ Sh(C)` induced by the continuous and
cocontinuous localization functor `forget K : OverSite K ⥤ C`. -/
noncomputable def localizationMorphism :
    MorphismOfTopoiIn J (overTopology J K) :=
  (forget K).morphismOfTopoiInOfCocontinuous (overTopology J K) J

end CategoryTheory.SemiRepresentableFamily
