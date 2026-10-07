module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_16_2_Comparison
public import stacks_project.Chap85.Lemma_85_16_2_Shriek

/-!
# Lemma 85.16.2

With the notation of Lemma 85.16.1, lower shriek along `j_total` exists on sheaves
and on abelian sheaves, inverse image along `j_total` is degreewise inverse image along
`j_n`, and abelian direct image `a_*` is the equalizer of `j_{0,*} G_0 ⇉ j_{1,*} G_1`.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))
variable [HasWeakSheafify J (Type (max w u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
  (totalForget K).op.HasLeftKanExtension P]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
  (totalForget K).op.HasLeftKanExtension P]

/-- Lemma 85.16.2 (1): With assumption and notation as in Lemma 85.16.1, there is a functor
`a^{Sh}_! : Sh((C / K)_total) ⥤ Sh(C)` left adjoint to `a⁻¹ : Sh(C) ⥤ Sh((C / K)_total)`.
Here `a^{Sh}_!` is `sheafLowerShriek` and `a⁻¹` is continuous sheaf pushforward of
`totalForget`, isomorphic to `totalLocalization.inverseImage` by
`CocontinuousPullback.comparison`. -/
@[stacks 09WM]
def sheafLowerShriekAdjunction :
    sheafLowerShriek J K ⊣
      (totalForget K).sheafPushforwardContinuous (Type (max w u v))
        (overSiteTotalTopology J K) J :=
  (totalForget K).sheafAdjunctionContinuous (Type (max w u v)) (overSiteTotalTopology J K) J

/-- Lemma 85.16.2 (2): With assumption and notation as in Lemma 85.16.1, there is a functor
`a_! : Ab((C / K)_total) ⥤ Ab(C)` left adjoint to `a⁻¹ : Ab(C) ⥤ Ab((C / K)_total)`.
Here `a_!` is `abelianLowerShriek` and `a⁻¹` is continuous sheaf pushforward of
`totalForget` on `AddCommGrpCat`. -/
@[stacks 09WM]
def abelianLowerShriekAdjunction :
    abelianLowerShriek J K ⊣
      (totalForget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
        (overSiteTotalTopology J K) J :=
  (totalForget K).sheafAdjunctionContinuous AddCommGrpCat.{max w u v}
    (overSiteTotalTopology J K) J

/-- Lemma 85.16.2 (3): With assumption and notation as in Lemma 85.16.1, the functor `a⁻¹`
associates to `F` in `Sh(C)` the sheaf on `(C / K)_total` which in degree `n` is equal to
`a_n⁻¹ F`. Here `G_n` means restriction along `ι`, and `a_n⁻¹` is continuous sheaf
pushforward of `forget (K.obj (op n))`, isomorphic to
`localizationMorphism.inverseImage`. -/
@[stacks 09WM]
def inverseImage_fiberRestrict (n : SimplexCategory) :
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
        (overSiteTotalTopology J K) J ⋙ sheafFiberRestrict J K n ≅
      sheafStageRestrict J K n :=
  sheafInverseImage_fiberRestrict J K n

/-- Degree-`n` evaluation of inverse image along `j_total`: the restriction of `a⁻¹ F`
is `a_n⁻¹ F`. -/
def inverseImage_fiberRestrict_app (n : SimplexCategory)
    (F : Sheaf J (Type (max w u v))) :
    (sheafFiberRestrict J K n).obj
        (((totalForget K).sheafPushforwardContinuous (Type (max w u v))
            (overSiteTotalTopology J K) J).obj F) ≅
      (sheafStageRestrict J K n).obj F :=
  (inverseImage_fiberRestrict J K n).app F

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
  (totalForget K).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (i : Fin 2) (P : (OverSite (K.obj (op ⦋1⦌)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (overSiteFace K i).op.HasPointwiseRightKanExtension P]
variable [∀ (i : Fin 2) (P : (OverSite (K.obj (op ⦋1⦌)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (overSiteFace K i ⋙ forget (K.obj (op ⦋0⦌))).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf J AddCommGrpCat.{max w u v})]

/-- Lemma 85.16.2 (4): With assumption and notation as in Lemma 85.16.1, the functor `a_*`
associates to `G` in `Ab((C / K)_total)` the equalizer of the two maps
`j_{0,*} G_0 ⇉ j_{1,*} G_1`. Here `j_{n,*}` is cocontinuous sheaf pushforward of
`forget (K.obj (op n))` and `a_*` is cocontinuous sheaf pushforward of `totalForget`. -/
@[stacks 09WM]
theorem abelianPushforwardToEqualizer_isIso
    (G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) :
    IsIso (abelianPushforwardToEqualizer J K G) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
