/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_16_1_Diagram
public import stacks_project.Chap85.Lemma_85_16_1_Localization

/-!
# Lemma 85.16.1

The localization `j_0 : C / K_0 ⥤ C` is a case-B augmentation of the simplicial
site `n ↦ C / K_n`. The morphisms of topoi `a_n` and `a` of Lemma 85.4.2 are
isomorphic to the morphisms presented by `j_n` and `j_total`.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (K : SimplicialObject (FormalCoproduct.{w} C))

/-- Lemma 85.16.1 (1): Let `C` be a site and `K` a simplicial object of `SR(C)`.
The localization functor `j_0 = forget (K.obj (op ⦋0⦌))` equalizes every pair of
operators `φ, ψ : ⦋0⦌ ⟶ n` after composing with `overMap`, and therefore presents
a case-B augmentation `a_0 : Sh(C / K_0) ⟶ Sh(C)` as in Remark 85.4.1. -/
@[stacks 0D8B]
theorem forget_comp_overMap_eq {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n) :
    overMap (K.map φ.op) ⋙ forget (K.obj (op ⦋0⦌)) =
      overMap (K.map ψ.op) ⋙ forget (K.obj (op ⦋0⦌)) :=
  sorry

variable (J : GrothendieckTopology C)
variable [HasSheafify J (Type (max w u v))]
variable [HasWeakSheafify J (Type (max w u v))]
variable [HasSheafify (overSiteTotalTopology J K) (Type (max w u v))]
variable [∀ n : SimplexCategoryᵒᵖ, HasSheafify (overTopology J (K.obj n)) (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
  (totalForget K).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
  (augmentationTotalForget K).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type (max w u v)),
  (stageForget K n).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategoryᵒᵖ) (P : (OverSite (K.obj n))ᵒᵖ ⥤ Type (max w u v)),
  (forget (K.obj n)).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.16.1 (2): The morphism of topoi `a_n : Sh(C / K_n) ⟶ Sh(C)` of
Lemma 85.4.2, presented by the common composite `u_n = j_0 ∘ u_φ`, is isomorphic
to the morphism of topoi associated to the continuous and cocontinuous localization
`j_n = forget (K.obj (op n))`. -/
@[stacks 0D8B]
def stageTopos_iso_localizationMorphism (n : SimplexCategory) :
    (stageTopos J K n).pushforward ≅
      (localizationMorphism J (K.obj (op n))).pushforward :=
  Functor.sheafPushforwardCocontinuousIso
    (overTopology J (K.obj (op n))) J (stageForget K n) (stageForget_iso_forget K n)

/-- Lemma 85.16.1 (3): The morphism of topoi `a : Sh((C / K)_total) ⟶ Sh(C)` of
Lemma 85.4.2, presented by the functor sending a degree-`n` object `U` to `u_n(U)`,
is isomorphic to the morphism of topoi associated to the continuous and cocontinuous
localization `j_total = totalForget K`. -/
@[stacks 0D8B]
def totalTopos_iso_totalLocalization :
    (totalTopos J K).pushforward ≅ (totalLocalization J K).pushforward :=
  Functor.sheafPushforwardCocontinuousIso
    (overSiteTotalTopology J K) J (augmentationTotalForget K)
    (augmentationTotalForget_iso_totalForget K)

end CategoryTheory.SemiRepresentableFamily
