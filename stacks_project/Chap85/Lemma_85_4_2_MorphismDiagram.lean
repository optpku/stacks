/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationTopos
import StacksCheckRecall
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap85.Lemma_85_3_4_Comparison
public import stacks_project.Chap85.Lemma_85_3_5_Stage
public import stacks_project.Chap85.Remark_85_4_1_MorphismDiagram

/-!
# Augmentation morphisms of topoi, covariant case

An exact-site augmentation `u0` of a morphism diagram induces stage morphisms of
topoi `a_n` and a total morphism `a : Sh(C_total) ⟶ Sh(D)` whose inverse image is
the sheaf system of the functors `a_n⁻¹` and whose direct image is the equalizer of
the two coface maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
include h_morphism
include h_aug

/-- Structure-map morphism of topoi `f_φ` of the ambient morphism diagram. -/
abbrev IsAugmentation.faceTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoiIn (J m).toGrothendieck (J n).toGrothendieck :=
  SimplicialSites.toposMap.{u, v, w} C J φ

/- Lemma 85.4.2: case A, stageTopos. -/
@[stacks 0D70] #check (CategoryTheory.SimplicialSites.IsAugmentation.stageTopos C J K u0 :
    ∀ (n : SimplexCategory),
    MorphismOfTopoiIn K.toGrothendieck (J n).toGrothendieck)

#check (CategoryTheory.SimplicialSites.IsAugmentation.stageTopos_inverseImage C J K u0 :
    ∀ (n : SimplexCategory),
    (IsAugmentation.stageTopos C J K u0 n)⁻¹ =
      (IsAugmentation.stageFunctor C u0 n).sheafPullback (Type w)
        K.toGrothendieck (J n).toGrothendieck)

/- Lemma 85.4.2: case A, totalTopos. -/
@[stacks 0D70] #check (CategoryTheory.SimplicialSites.IsAugmentation.totalTopos C J K u0 :
    MorphismOfTopoiIn K.toGrothendieck (topology C J))

#check (CategoryTheory.SimplicialSites.IsAugmentation.totalTopos_inverseImage C J K u0 :
    (IsAugmentation.totalTopos C J K u0)⁻¹ = IsAugmentation.inverseImage C J K u0)

/- Lemma 85.4.2: case A, stageTopos_comp. -/
@[stacks 0D70] #check (CategoryTheory.SimplicialSites.IsAugmentation.stageTopos_comp C J K u0 :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (IsAugmentation.stageTopos C J K u0 m)⁻¹ ⋙ (IsAugmentation.faceTopos C J φ)⁻¹ ≅
      (IsAugmentation.stageTopos C J K u0 n)⁻¹)

/- Lemma 85.4.2: case A, pushforwardFork_isLimit. -/
@[stacks 0D70] #check (CategoryTheory.SimplicialSites.IsAugmentation.pushforwardFork_isLimit C J K u0 :
    ∀ (F : Sheaf (topology C J) (Type w)),
    IsLimit (IsAugmentation.pushforwardFork C J K u0 F))

variable [∀ n, (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

/- Lemma 85.4.2: case A, totalTopos_comp_ofStage. -/
@[stacks 0D70] #check (CategoryTheory.SimplicialSites.IsAugmentation.totalTopos_comp_ofStage C J K u0 :
    ∀ (n : SimplexCategory),
    (IsAugmentation.totalTopos C J K u0)⁻¹ ⋙ (ofStageMorphism C J n)⁻¹ ≅
      (IsAugmentation.stageTopos C J K u0 n)⁻¹)

end CategoryTheory.SimplicialSites
