module

public import stacks_project.Chap85.Lemma_85_4_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_4_2_MorphismDiagram

/-!
# Lemma 85.4.2

In Situation 85.3.3 an augmentation `a0` towards a site `D` induces morphisms of
topoi `a_n : Sh(C_n) ⟶ Sh(D)` and a morphism of topoi
`a : Sh(C_total) ⟶ Sh(D)` such that `a_m ∘ f_φ = a_n`, `a ∘ g_n = a_n`, and
`a_* F` is the equalizer of the two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`.
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

/-- Lemma 85.4.2 (1): in Situation 85.3.3 case A, an augmentation `a0` towards a site `D`
induces a morphism of topoi `a_n : Sh(C.obj n) ⟶ Sh(D)` for every `n`. -/
@[stacks 0D70]
abbrev stageTopos (n : SimplexCategory) :
    MorphismOfTopoiIn K.toGrothendieck (J n).toGrothendieck :=
  IsAugmentation.stageTopos C J K u0 n

/-- Inverse image of the case A stage morphism `a_n` is sheaf pullback along `u_n`. -/
theorem stageTopos_inverseImage (n : SimplexCategory) :
    (stageTopos C J K u0 n)⁻¹ =
      (IsAugmentation.stageFunctor C u0 n).sheafPullback (Type w)
        K.toGrothendieck (J n).toGrothendieck :=
  sorry

/-- Lemma 85.4.2 (2): in Situation 85.3.3 case A, the augmentation induces a morphism of
topoi `a : Sh(C_total) ⟶ Sh(D)`. -/
@[stacks 0D70]
abbrev totalTopos : MorphismOfTopoiIn K.toGrothendieck (topology C J) :=
  IsAugmentation.totalTopos C J K u0

/-- Inverse image of the case A total morphism is assembled from the functors `a_n⁻¹`. -/
theorem totalTopos_inverseImage :
    (totalTopos C J K u0)⁻¹ = IsAugmentation.inverseImage C J K u0 :=
  sorry

/-- Lemma 85.4.2 (3): in Situation 85.3.3 case A, `a_m ∘ f_φ = a_n` for every
simplex operator `φ : m ⟶ n`. -/
@[stacks 0D70]
abbrev stageTopos_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageTopos C J K u0 m)⁻¹ ⋙ (IsAugmentation.faceTopos C J φ)⁻¹ ≅
      (stageTopos C J K u0 n)⁻¹ :=
  IsAugmentation.stageTopos_comp C J K u0 φ

/-- Lemma 85.4.2 (5): in Situation 85.3.3 case A, `a_* F` is the equalizer of the two
maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
@[stacks 0D70]
abbrev pushforwardFork_isLimit (F : Sheaf (topology C J) (Type w)) :
    IsLimit (IsAugmentation.pushforwardFork C J K u0 F) :=
  IsAugmentation.pushforwardFork_isLimit C J K u0 F

variable [∀ n, (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.4.2 (4): in Situation 85.3.3 case A, `a ∘ g_n = a_n` for the degree-`n`
inclusion morphism of topoi `g_n` of Lemma 85.3.5. -/
@[stacks 0D70]
abbrev totalTopos_comp_ofStage (n : SimplexCategory) :
    (totalTopos C J K u0)⁻¹ ⋙ (ofStageMorphism C J n)⁻¹ ≅
      (stageTopos C J K u0 n)⁻¹ :=
  IsAugmentation.totalTopos_comp_ofStage C J K u0 n

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_augB : IsAugmentation F J K u0]
include h_fiberwise
include h_augB

/-- Lemma 85.4.2 (6): in Situation 85.3.3 case B, an augmentation `a0` towards a site `D`
induces a morphism of topoi `a_n : Sh(C_n) ⟶ Sh(D)` for every `n`. -/
@[stacks 0D70]
abbrev stageTopos (n : SimplexCategory) :
    MorphismOfTopoiIn K.toGrothendieck (J (op n)).toGrothendieck :=
  IsAugmentation.stageTopos F J K u0 n

/-- Inverse image of the case B stage morphism `a_n` is cocontinuous sheaf pullback along `u_n`. -/
theorem stageTopos_inverseImage (n : SimplexCategory) :
    (stageTopos F J K u0 n)⁻¹ =
      (IsAugmentation.stageFunctor F u0 n).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck K.toGrothendieck :=
  sorry

/-- Lemma 85.4.2 (7): in Situation 85.3.3 case B, the augmentation induces a morphism of
topoi `a : Sh(C_total) ⟶ Sh(D)`. -/
@[stacks 0D70]
abbrev totalTopos : MorphismOfTopoiIn K.toGrothendieck (topology F J) :=
  IsAugmentation.totalTopos F J K u0

/-- Inverse image of the case B total morphism is assembled from the functors `a_n⁻¹`. -/
theorem totalTopos_inverseImage :
    (totalTopos F J K u0)⁻¹ = IsAugmentation.inverseImage F J K u0 :=
  sorry

/-- Lemma 85.4.2 (8): in Situation 85.3.3 case B, `a_m ∘ f_φ = a_n` for every
simplex operator `φ : m ⟶ n`. -/
@[stacks 0D70]
abbrev stageTopos_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageTopos F J K u0 m)⁻¹ ⋙ (IsAugmentation.faceTopos F J φ)⁻¹ ≅
      (stageTopos F J K u0 n)⁻¹ :=
  IsAugmentation.stageTopos_comp F J K u0 φ

/-- Lemma 85.4.2 (10): in Situation 85.3.3 case B, `a_* F` is the equalizer of the two
maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
@[stacks 0D70]
abbrev pushforwardFork_isLimit (G : Sheaf (topology F J) (Type w)) :
    IsLimit (IsAugmentation.pushforwardFork F J K u0 G) :=
  IsAugmentation.pushforwardFork_isLimit F J K u0 G

variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.4.2 (9): in Situation 85.3.3 case B, `a ∘ g_n = a_n` for the degree-`n`
fiber morphism of topoi `g_n` of Lemma 85.3.5. -/
@[stacks 0D70]
abbrev totalTopos_comp_fiberMorphism (n : SimplexCategory) :
    (totalTopos F J K u0)⁻¹ ⋙ (fiberMorphism F J n)⁻¹ ≅
      (stageTopos F J K u0 n)⁻¹ :=
  IsAugmentation.totalTopos_comp_fiberMorphism F J K u0 n

end CategoryTheory.Grothendieck
