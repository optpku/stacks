module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Comparison

/-!
# Lemma 85.16.2

With the notation of Lemma 85.16.1, lower shriek along `j_total` exists on sheaves
and on abelian sheaves, inverse image along `j_total` is degreewise inverse image along
`j_n`, and abelian direct image `a_*` is the equalizer of `j_{0,*} G_0 ⇉ j_{1,*} G_1`.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

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

/- Lower shriek on sheaves of sets is left adjoint to total inverse image. -/
#check (CategoryTheory.Functor.sheafAdjunctionContinuous (totalForget K)
    (Type (max w u v)) (overSiteTotalTopology J K) J :
  (totalForget K).sheafPullback (Type (max w u v)) (overSiteTotalTopology J K) J ⊣
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
      (overSiteTotalTopology J K) J)

/- Lower shriek on abelian sheaves is left adjoint to total inverse image. -/
#check (CategoryTheory.Functor.sheafAdjunctionContinuous (totalForget K)
    AddCommGrpCat.{max w u v} (overSiteTotalTopology J K) J :
  (totalForget K).sheafPullback AddCommGrpCat.{max w u v} (overSiteTotalTopology J K) J ⊣
    (totalForget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
      (overSiteTotalTopology J K) J)

/- Total inverse image restricts degreewise to stage inverse image. -/
#check (CategoryTheory.SemiRepresentableFamily.sheafInverseImage_fiberRestrict J K :
  ∀ n : SimplexCategory,
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
        (overSiteTotalTopology J K) J ⋙ sheafFiberRestrict J K n ≅
      sheafStageRestrict J K n)

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

/- Lemma 85.16.2. Total localization admits lower shriek on sheaves of sets and abelian
sheaves, its inverse image is degreewise stage inverse image, and its abelian direct image
is canonically the equalizer of the two coface direct-image maps. -/
@[stacks 09WM] #check
  (CategoryTheory.SemiRepresentableFamily.abelianPushforwardToEqualizer_isIso J K :
    ∀ G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v},
      IsIso (abelianPushforwardToEqualizer J K G))

end CategoryTheory.SemiRepresentableFamily
