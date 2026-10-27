/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Augmentation Čech cochains of abelian sheaves

Stage direct images and restriction-induced transitions form a cosimplicial sheaf.
Its alternating-coface complex extends to an integer-indexed cochain with the
equalizer direct image in degree `-1`.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{w})]
include h_morphism
include h_aug

/-- Stage direct image `a_{n,*}` of abelian sheaves, i.e. continuous sheaf
pushforward along the common composite `u_n`. -/
def IsAugmentation.abelianStagePushforward (n : SimplexCategory) :
    Sheaf (J n).toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  (IsAugmentation.stageFunctor C u0 n).sheafPushforwardContinuous AddCommGrpCat.{w}
    K.toGrothendieck (J n).toGrothendieck

/-- `abelianStagePushforward n` is continuous sheaf pushforward along `u_n`. -/
theorem IsAugmentation.abelianStagePushforward_eq (n : SimplexCategory) :
    IsAugmentation.abelianStagePushforward C J K u0 n =
      (IsAugmentation.stageFunctor C u0 n).sheafPushforwardContinuous AddCommGrpCat.{w}
        K.toGrothendieck (J n).toGrothendieck := sorry

/-- Adjunction `a_n⁻¹ ⊣ a_{n,*}` on abelian sheaves. -/
def IsAugmentation.abelianStagePushforward_adjunction (n : SimplexCategory) :
    IsAugmentation.abelianStageInverseImage C J K u0 n ⊣
      IsAugmentation.abelianStagePushforward C J K u0 n :=
  (IsAugmentation.stageFunctor C u0 n).sheafAdjunctionContinuous AddCommGrpCat.{w}
    K.toGrothendieck (J n).toGrothendieck

/-- Direct-image mate of `a_m ∘ f_φ = a_n` on abelian sheaves. -/
def IsAugmentation.abelianStagePushforward_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck ⋙
      IsAugmentation.abelianStagePushforward C J K u0 m ≅
    IsAugmentation.abelianStagePushforward C J K u0 n :=
  Functor.sheafPushforwardContinuousComp'
    (IsAugmentation.stageFunctor_compIso C J K u0 φ) AddCommGrpCat.{w}
    K.toGrothendieck (J m).toGrothendieck (J n).toGrothendieck

omit h_morphism h_aug in
/-- Restriction along a total-category simplex arrow is natural within its source stage. -/
private theorem stageRestrictMap_naturality (F : Sheaf (topology C J) AddCommGrpCat.{w})
    {m n : SimplexCategory} (φ : m ⟶ n)
    {V W : (C.obj m)ᵒᵖ} (η : V ⟶ W) :
    ((stageRestrict C J AddCommGrpCat.{w} m).obj F).obj.map η ≫
        F.obj.map (stageHom C φ W.unop).op =
      F.obj.map (stageHom C φ V.unop).op ≫
        ((C.map φ).toFunctor.op ⋙
          ((stageRestrict C J AddCommGrpCat.{w} n).obj F).obj).map η := sorry

/-- Restriction of `F` along the total-category arrow `(φ, 𝟙) : u_φ(V) ⟶ V`. -/
def stageRestrictMap (F : Sheaf (topology C J) AddCommGrpCat.{w})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageRestrict C J AddCommGrpCat.{w} m).obj F ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck).obj
        ((stageRestrict C J AddCommGrpCat.{w} n).obj F) :=
  ObjectProperty.homMk
    { app := fun V ↦ F.obj.map (stageHom C φ V.unop).op
      naturality := fun _ _ η ↦ stageRestrictMap_naturality C J F φ η }

/-- The structure map `a_{m,*} F_m ⟶ a_{n,*} F_n` induced by a simplex operator
`φ : m ⟶ n`. -/
def abelianStagePushforward_map (F : Sheaf (topology C J) AddCommGrpCat.{w})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.abelianStagePushforward C J K u0 m).obj
      ((stageRestrict C J AddCommGrpCat.{w} m).obj F) ⟶
    (IsAugmentation.abelianStagePushforward C J K u0 n).obj
      ((stageRestrict C J AddCommGrpCat.{w} n).obj F) :=
  (IsAugmentation.abelianStagePushforward C J K u0 m).map (stageRestrictMap C J F φ) ≫
    (IsAugmentation.abelianStagePushforward_comp C J K u0 φ).hom.app
      ((stageRestrict C J AddCommGrpCat.{w} n).obj F)

/-- The two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1` induced by the coface operators `δ i`. -/
def abelianPushforwardParallel (F : Sheaf (topology C J) AddCommGrpCat.{w}) (i : Fin 2) :
    (IsAugmentation.abelianStagePushforward C J K u0 ⦋0⦌).obj
      ((stageRestrict C J AddCommGrpCat.{w} ⦋0⦌).obj F) ⟶
    (IsAugmentation.abelianStagePushforward C J K u0 ⦋1⦌).obj
      ((stageRestrict C J AddCommGrpCat.{w} ⦋1⦌).obj F) :=
  abelianStagePushforward_map C J K u0 F (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)

/-- A morphism of total sheaves carries equalizing sections to equalizing sections. -/
private theorem IsAugmentation.abelianPushforwardMap_condition
    {A B : Sheaf (topology C J) AddCommGrpCat.{w}} (α : A ⟶ B) :
    (equalizer.ι (abelianPushforwardParallel C J K u0 A 0)
        (abelianPushforwardParallel C J K u0 A 1) ≫
      (IsAugmentation.abelianStagePushforward C J K u0 ⦋0⦌).map
        ((stageRestrict C J AddCommGrpCat.{w} ⦋0⦌).map α)) ≫
        abelianPushforwardParallel C J K u0 B 0 =
      (equalizer.ι (abelianPushforwardParallel C J K u0 A 0)
        (abelianPushforwardParallel C J K u0 A 1) ≫
      (IsAugmentation.abelianStagePushforward C J K u0 ⦋0⦌).map
        ((stageRestrict C J AddCommGrpCat.{w} ⦋0⦌).map α)) ≫
        abelianPushforwardParallel C J K u0 B 1 := sorry

/-- The equalizer morphism induced by a morphism of total sheaves. -/
private def IsAugmentation.abelianPushforwardMap
    {A B : Sheaf (topology C J) AddCommGrpCat.{w}} (α : A ⟶ B) :
    equalizer (abelianPushforwardParallel C J K u0 A 0)
      (abelianPushforwardParallel C J K u0 A 1) ⟶
      equalizer (abelianPushforwardParallel C J K u0 B 0)
        (abelianPushforwardParallel C J K u0 B 1) :=
  equalizer.lift (equalizer.ι (abelianPushforwardParallel C J K u0 A 0)
        (abelianPushforwardParallel C J K u0 A 1) ≫
      (IsAugmentation.abelianStagePushforward C J K u0 ⦋0⦌).map
        ((stageRestrict C J AddCommGrpCat.{w} ⦋0⦌).map α))
    (IsAugmentation.abelianPushforwardMap_condition C J K u0 α)

/-- The induced equalizer morphisms preserve identities and composition. -/
private theorem IsAugmentation.abelianPushforwardMap_laws :
    (∀ A : Sheaf (topology C J) AddCommGrpCat.{w},
      IsAugmentation.abelianPushforwardMap C J K u0 (𝟙 A) =
        𝟙 (equalizer (abelianPushforwardParallel C J K u0 A 0)
          (abelianPushforwardParallel C J K u0 A 1))) ∧
    (∀ {A B E : Sheaf (topology C J) AddCommGrpCat.{w}} (α : A ⟶ B) (β : B ⟶ E),
      IsAugmentation.abelianPushforwardMap C J K u0 (α ≫ β) =
        IsAugmentation.abelianPushforwardMap C J K u0 α ≫
          IsAugmentation.abelianPushforwardMap C J K u0 β) := sorry

/-- Direct image `a_*` of abelian sheaves, sending `F` to the equalizer of
`a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def IsAugmentation.abelianPushforward :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} where
  obj F :=
    equalizer (abelianPushforwardParallel C J K u0 F 0)
      (abelianPushforwardParallel C J K u0 F 1)
  map α := IsAugmentation.abelianPushforwardMap C J K u0 α
  map_id A := (IsAugmentation.abelianPushforwardMap_laws C J K u0).1 A
  map_comp α β := (IsAugmentation.abelianPushforwardMap_laws C J K u0).2 α β

/-- The object `a_* F` is the equalizer of the two coface maps. -/
theorem IsAugmentation.abelianPushforward_obj
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (IsAugmentation.abelianPushforward C J K u0).obj F =
      equalizer (abelianPushforwardParallel C J K u0 F 0)
        (abelianPushforwardParallel C J K u0 F 1) := sorry

/-- The comparison `a_* F ⟶ a_{0,*} F_0`. -/
def IsAugmentation.abelianPushforwardι
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (IsAugmentation.abelianPushforward C J K u0).obj F ⟶
      (IsAugmentation.abelianStagePushforward C J K u0 ⦋0⦌).obj
        ((stageRestrict C J AddCommGrpCat.{w} ⦋0⦌).obj F) :=
  equalizer.ι (abelianPushforwardParallel C J K u0 F 0)
    (abelianPushforwardParallel C J K u0 F 1)

/-- The simplex transition maps preserve identities and composition. -/
private theorem pushforwardCosimplicial_laws (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (∀ n : SimplexCategory,
      abelianStagePushforward_map C J K u0 F (𝟙 n) =
        𝟙 ((IsAugmentation.abelianStagePushforward C J K u0 n).obj
          ((stageRestrict C J AddCommGrpCat.{w} n).obj F))) ∧
    (∀ {l m n : SimplexCategory} (φ : l ⟶ m) (ψ : m ⟶ n),
      abelianStagePushforward_map C J K u0 F (φ ≫ ψ) =
        abelianStagePushforward_map C J K u0 F φ ≫
          abelianStagePushforward_map C J K u0 F ψ) := sorry

/-- The cosimplicial abelian sheaf `n ↦ a_{n,*} F_n` on `D`. -/
def pushforwardCosimplicial (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CosimplicialObject (Sheaf K.toGrothendieck AddCommGrpCat.{w}) where
  obj n :=
    (IsAugmentation.abelianStagePushforward C J K u0 n).obj
      ((stageRestrict C J AddCommGrpCat.{w} n).obj F)
  map φ := abelianStagePushforward_map C J K u0 F φ
  map_id n := (pushforwardCosimplicial_laws C J K u0 F).1 n
  map_comp φ ψ := (pushforwardCosimplicial_laws C J K u0 F).2 φ ψ

/-- Degree `n` of `pushforwardCosimplicial` is the abelian sheaf `a_{n,*} F_n`. -/
theorem pushforwardCosimplicial_obj (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    (pushforwardCosimplicial C J K u0 F).obj n =
      (IsAugmentation.abelianStagePushforward C J K u0 n).obj
        ((stageRestrict C J AddCommGrpCat.{w} n).obj F) := sorry

/-- The unaugmented cochain `a_{0,*} F_0 → a_{1,*} F_1 → ⋯` of abelian sheaves on
`D`. -/
abbrev cechComplex (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℕ :=
  (alternatingCofaceMapComplex _).obj (pushforwardCosimplicial C J K u0 F)

/-- Degree `n` of `cechComplex` is `a_{n,*} F_n`. -/
theorem cechComplex_X (F : Sheaf (topology C J) AddCommGrpCat.{w}) (n : ℕ) :
    (cechComplex C J K u0 F).X n = (pushforwardCosimplicial C J K u0 F).obj ⦋n⦌ := sorry

/-- Differentials of `cechComplex` are the alternating sums of coface maps. -/
theorem cechComplex_d_eq (F : Sheaf (topology C J) AddCommGrpCat.{w}) (n : ℕ) :
    (cechComplex C J K u0 F).d n (n + 1) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • (pushforwardCosimplicial C J K u0 F).δ i := sorry

/-- The connecting differential `a_* F ⟶ a_{0,*} F_0` from `single₀ (a_* F)` into
the unaugmented cochain. -/
def cechConnect_d₀ (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj
        ((IsAugmentation.abelianPushforward C J K u0).obj F)).X 0 ⟶
      (cechComplex C J K u0 F).X 0 :=
  IsAugmentation.abelianPushforwardι C J K u0 F

/-- The connecting differential is the equalizer comparison `a_* F ⟶ a_{0,*} F_0`. -/
theorem cechConnect_d₀_eq (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    cechConnect_d₀ C J K u0 F = IsAugmentation.abelianPushforwardι C J K u0 F := sorry

/-- The connecting differential annihilates the outgoing differential of
`single₀ (a_* F)`. -/
theorem cechConnect_comp_d₀ (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj
          ((IsAugmentation.abelianPushforward C J K u0).obj F)).d 1 0 ≫
        cechConnect_d₀ C J K u0 F = 0 := sorry

/-- The connecting differential equalizes the first coface of the unaugmented
cochain. -/
theorem cechConnect_d₀_comp (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    cechConnect_d₀ C J K u0 F ≫ (cechComplex C J K u0 F).d 0 1 = 0 := sorry

/-- Connecting data for the ℤ-indexed cochain, with `a_* F` in degree `-1`. -/
def cechConnect (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj ((IsAugmentation.abelianPushforward C J K u0).obj F))
      (cechComplex C J K u0 F) where
  d₀ := cechConnect_d₀ C J K u0 F
  comp_d₀ := cechConnect_comp_d₀ C J K u0 F
  d₀_comp := cechConnect_d₀_comp C J K u0 F

/-- The canonical cochain `0 → a_* F → a_{0,*} F_0 → a_{1,*} F_1 → ⋯` of abelian
sheaves on `D`. -/
def augmentationCechCochain (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℤ :=
  (cechConnect C J K u0 F).cochainComplex

/-- Degree `-1` of `augmentationCechCochain` is the abelian sheaf `a_* F`. -/
theorem augmentationCechCochain_X_negOne
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (augmentationCechCochain C J K u0 F).X (-1) =
      (IsAugmentation.abelianPushforward C J K u0).obj F := sorry

/-- Degree `n ≥ 0` of `augmentationCechCochain` is `a_{n,*} F_n`. -/
theorem augmentationCechCochain_X_ofNat
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) (n : ℕ) :
    (augmentationCechCochain C J K u0 F).X n =
      (IsAugmentation.abelianStagePushforward C J K u0 ⦋n⦌).obj
        ((stageRestrict C J AddCommGrpCat.{w} ⦋n⦌).obj F) := sorry

/-- The differential out of degree `-1` is the comparison `a_* F ⟶ a_{0,*} F_0`. -/
theorem augmentationCechCochain_d_negOne_zero
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (augmentationCechCochain C J K u0 F).d (-1) 0 = cechConnect_d₀ C J K u0 F := sorry

/-- The augmented Čech cochain is exact in degrees `-1` and `0`. -/
theorem augmentationCechCochain_exactAt_negOne_zero
    (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (augmentationCechCochain C J K u0 F).ExactAt n := sorry

/-- The augmented Čech cochain of an injective total sheaf is acyclic. -/
theorem augmentationCechCochain_acyclic_of_injective
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) [Injective F] :
    (augmentationCechCochain C J K u0 F).Acyclic := sorry

end CategoryTheory.SimplicialSites
