/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Comparison
public import ReasLib.CategoryTheory.Sites.Topos.Composition

/-!
# Push-pull Čech complexes of simplicial families
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]

/-- Inverse image `a_n⁻¹` along localization at `K_n`, as continuous sheaf pushforward of
`forget (K_n)`. -/
def abelianStageInverseImage (n : SimplexCategory) :
    Sheaf J AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.obj (op n))) AddCommGrpCat.{max w u v} :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (forget (K.obj (op n)))
    AddCommGrpCat.{max w u v} _ (overTopology J (K.obj (op n))) J
    (forget_isContinuous J (K.obj (op n)))

/-- Direct image along the relocalization induced by a simplex operator. -/
def abelianFacePushforwardMap {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf (overTopology J (K.obj (op n))) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.obj (op m))) AddCommGrpCat.{max w u v} :=
  (overMap (K.map φ.op)).sheafPushforwardCocontinuous
    AddCommGrpCat.{max w u v}
    (overTopology J (K.obj (op n)))
    (overTopology J (K.obj (op m)))

/-- Inverse image along the relocalization induced by a simplex operator. -/
def abelianFaceInverseImageMap {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf (overTopology J (K.obj (op m))) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.obj (op n))) AddCommGrpCat.{max w u v} :=
  (overMap (K.map φ.op)).sheafPushforwardContinuous
    AddCommGrpCat.{max w u v}
    (overTopology J (K.obj (op n)))
    (overTopology J (K.obj (op m)))

/-- Adjunction `v⁻¹ ⊣ v_*` for relocalization along a simplex operator. -/
def abelianFaceAdjunctionMap {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianFaceInverseImageMap J K φ ⊣ abelianFacePushforwardMap J K φ :=
  (overMap (K.map φ.op)).sheafAdjunctionCocontinuous
    AddCommGrpCat.{max w u v}
    (overTopology J (K.obj (op n)))
    (overTopology J (K.obj (op m)))

/-- Inverse-image identification `a_n⁻¹ ≅ a_m⁻¹ ⋙ v⁻¹`. -/
def abelianStageInverseImage_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianStageInverseImage J K m ⋙ abelianFaceInverseImageMap J K φ ≅
      abelianStageInverseImage J K n :=
  Functor.sheafPushforwardContinuousComp' (overMap_forget (K.map φ.op))
    AddCommGrpCat.{max w u v}
    (overTopology J (K.obj (op n)))
    (overTopology J (K.obj (op m))) J

/-- Direct-image identification `v_* ⋙ j_{m,*} ≅ j_{n,*}`. -/
def abelianFace_comp_stagePushforwardMap {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianFacePushforwardMap J K φ ⋙
        abelianStagePushforward J K m ≅
      abelianStagePushforward J K n :=
  Functor.sheafPushforwardCocontinuousComp'
    (overTopology J (K.obj (op n)))
    (overTopology J (K.obj (op m))) J
    (overMap (K.map φ.op)) (forget (K.obj (op m)))
    (overMap_forget (K.map φ.op))

/-- The structure map `j_{m,*} j_m⁻¹ F ⟶ j_{n,*} j_n⁻¹ F` induced by `φ : m ⟶ n`. -/
def abelianStagePushforward_map (F : Sheaf J AddCommGrpCat.{max w u v})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianStagePushforward J K m).obj
        ((abelianStageInverseImage J K m).obj F) ⟶
      (abelianStagePushforward J K n).obj
        ((abelianStageInverseImage J K n).obj F) :=
  (abelianStagePushforward J K m).map
      ((abelianFaceAdjunctionMap J K φ).unit.app
        ((abelianStageInverseImage J K m).obj F)) ≫
    (abelianStagePushforward J K m).map
      ((abelianFacePushforwardMap J K φ).map
        ((abelianStageInverseImage_comp J K φ).hom.app F)) ≫
    (abelianFace_comp_stagePushforwardMap J K φ).hom.app
      ((abelianStageInverseImage J K n).obj F)

/-- Identity simplex operators act as identity on push-pull. -/
theorem abelianStagePushforward_map_id (F : Sheaf J AddCommGrpCat.{max w u v})
    (n : SimplexCategory) :
    abelianStagePushforward_map J K F (𝟙 n) = 𝟙 _ :=
  sorry

/-- Structure maps of push-pull respect composition of simplex operators. -/
theorem abelianStagePushforward_map_comp (F : Sheaf J AddCommGrpCat.{max w u v})
    {m n p : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ p) :
    abelianStagePushforward_map J K F (φ ≫ ψ) =
      abelianStagePushforward_map J K F φ ≫ abelianStagePushforward_map J K F ψ :=
  sorry

/-- The cosimplicial abelian sheaf `n ↦ j_{n,*} j_n⁻¹ F`. -/
def cechCosimplicial (F : Sheaf J AddCommGrpCat.{max w u v}) :
    CosimplicialObject (Sheaf J AddCommGrpCat.{max w u v}) where
  obj n :=
    (abelianStagePushforward J K n).obj
      ((abelianStageInverseImage J K n).obj F)
  map φ := abelianStagePushforward_map J K F φ
  map_id n := abelianStagePushforward_map_id J K F n
  map_comp φ ψ := abelianStagePushforward_map_comp J K F φ ψ

/-- Face maps of `cechCosimplicial` are the structure maps of `K`. -/
theorem cechCosimplicial_map (F : Sheaf J AddCommGrpCat.{max w u v})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (cechCosimplicial J K F).map φ = abelianStagePushforward_map J K F φ :=
  rfl

/-- The unaugmented Čech cochain `j_{0,*} j_0⁻¹ F → j_{1,*} j_1⁻¹ F → ⋯`. -/
def cechComplex (F : Sheaf J AddCommGrpCat.{max w u v}) :
    CochainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℕ :=
  (alternatingCofaceMapComplex _).obj (cechCosimplicial J K F)

/-- Degree `n` of `cechComplex` is `j_{n,*} j_n⁻¹ F`. -/
theorem cechComplex_X (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (cechComplex J K F).X n =
      (abelianStagePushforward J K ⦋n⦌).obj
        ((abelianStageInverseImage J K ⦋n⦌).obj F) :=
  rfl

end CategoryTheory.SemiRepresentableFamily
