/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_15_1_Site
public import stacks_project.Chap85.Lemma_85_15_1

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

/-- Direct image along localization at `K` is the cocontinuous sheaf pushforward of
`forget K`. -/
theorem localizationMorphism_pushforward :
    (localizationMorphism J K).pushforward =
      (forget K).sheafPushforwardCocontinuous (Type (max w u v))
        (overTopology J K) J := sorry

/-- Inverse image along localization at `K` is the sheafified cocontinuous pullback
along `forget K`. -/
theorem localizationMorphism_inverseImage :
    (localizationMorphism J K).inverseImage =
      (forget K).sheafPullbackCocontinuous (Type (max w u v))
        (overTopology J K) J := sorry

end CategoryTheory.SemiRepresentableFamily
