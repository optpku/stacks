module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationTopos
import StacksCheckRecall
public import stacks_project.Chap07.Definition_7_20_1_Cocontinuous
public import stacks_project.Chap85.Lemma_85_3_4_Fiberwise
public import stacks_project.Chap85.Lemma_85_3_5_Fiber
public import stacks_project.Chap85.Remark_85_4_1_Fiberwise

/-!
# Augmentation morphisms of topoi, fiberwise case

A cocontinuous augmentation `u0` of a fiberwise simplicial site induces stage
morphisms of topoi `a_n` and a total morphism `a : Sh(C_total) ⟶ Sh(D)` whose
inverse image is the sheaf system of the functors `a_n⁻¹` and whose direct image
is the equalizer of the two coface maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`. The total
morphism is presented by the cocontinuous functor sending a degree-`n` object
`U` to `u_n(U)`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

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
variable [h_aug : IsAugmentation F J K u0]
include h_fiberwise
include h_aug

/-- Structure-map morphism of topoi `f_φ` of the ambient fiberwise site. -/
abbrev IsAugmentation.faceTopos {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoiIn (J (op m)).toGrothendieck (J (op n)).toGrothendieck :=
  Grothendieck.toposMap.{u, v, w} F J φ

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
