module

public import stacks_project.Chap85.Lemma_85_4_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_4_2_MorphismDiagram
import StacksCheckRecall

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

/- Lemma 85.4.2: case B, stageTopos. -/
@[stacks 0D70] #check (CategoryTheory.Grothendieck.IsAugmentation.stageTopos F J K u0 :
    ∀ (n : SimplexCategory),
    MorphismOfTopoiIn K.toGrothendieck (J (op n)).toGrothendieck)

#check (CategoryTheory.Grothendieck.IsAugmentation.stageTopos_inverseImage F J K u0 :
    ∀ (n : SimplexCategory),
    (IsAugmentation.stageTopos F J K u0 n)⁻¹ =
      (IsAugmentation.stageFunctor F u0 n).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck K.toGrothendieck)

/- Lemma 85.4.2: case B, totalTopos. -/
@[stacks 0D70] #check (CategoryTheory.Grothendieck.IsAugmentation.totalTopos F J K u0 :
    MorphismOfTopoiIn K.toGrothendieck (topology F J))

#check (CategoryTheory.Grothendieck.IsAugmentation.totalTopos_inverseImage F J K u0 :
    (IsAugmentation.totalTopos F J K u0)⁻¹ = IsAugmentation.inverseImage F J K u0)

/- Lemma 85.4.2: case B, stageTopos_comp. -/
@[stacks 0D70] #check (CategoryTheory.Grothendieck.IsAugmentation.stageTopos_comp F J K u0 :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (IsAugmentation.stageTopos F J K u0 m)⁻¹ ⋙ (IsAugmentation.faceTopos F J φ)⁻¹ ≅
      (IsAugmentation.stageTopos F J K u0 n)⁻¹)

/- Lemma 85.4.2: case B, pushforwardFork_isLimit. -/
@[stacks 0D70] #check (CategoryTheory.Grothendieck.IsAugmentation.pushforwardFork_isLimit F J K u0 :
    ∀ (G : Sheaf (topology F J) (Type w)),
    IsLimit (IsAugmentation.pushforwardFork F J K u0 G))

variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]

/- Lemma 85.4.2: case B, totalTopos_comp_fiberMorphism. -/
@[stacks 0D70] #check (CategoryTheory.Grothendieck.IsAugmentation.totalTopos_comp_fiberMorphism F J K u0 :
    ∀ (n : SimplexCategory),
    (IsAugmentation.totalTopos F J K u0)⁻¹ ⋙ (fiberMorphism F J n)⁻¹ ≅
      (IsAugmentation.stageTopos F J K u0 n)⁻¹)

end CategoryTheory.Grothendieck
