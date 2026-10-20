module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Family.Localization
public import ReasLib.CategoryTheory.Sites.Family.Topos
public import ReasLib.CategoryTheory.Sites.Family.Simplicial
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Comparison
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Cohomology
import StacksCheckRecall

universe w v u z

open CategoryTheory CategoryTheory.Limits CategoryTheory.SemiRepresentableFamily Opposite
open scoped Simplicial

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (X : C)
variable (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))

/- Semi-representable objects over X are formal coproducts in C/X. -/
#check (CategoryTheory.SemiRepresentableFamily.OverFamily.{v, u, w} X :
  Type (max (w + 1) u v))
#check (K : SimplicialObject (OverFamily X))
#check (CategoryTheory.GrothendieckTopology.over J X :
  GrothendieckTopology (CategoryTheory.Over X))
#check (CategoryTheory.SemiRepresentableFamily.overSiteDiagram K :
  SimplicialObject Cat.{max w u v, max w u v})

/- Remark 85.16.4 (Variant for over an object): the total site, its localization
functors and morphisms of topoi, lower shriek on sets and abelian groups, and
the section's results are obtained by applying the constructions to C/X. -/
@[stacks 0D8C] #check (CategoryTheory.SemiRepresentableFamily.overSiteTotalTopology
    (J.over X) K : GrothendieckTopology (Grothendieck (overSiteDiagram K)))

/- The total and stage localization functors land in C/X. -/
#check (CategoryTheory.SemiRepresentableFamily.totalForget K :
  Grothendieck (overSiteDiagram K) ⥤ CategoryTheory.Over X)

variable (n : SimplexCategoryᵒᵖ)

#check (CategoryTheory.SemiRepresentableFamily.forget (K.obj n) :
  OverSite (K.obj n) ⥤ CategoryTheory.Over X)

section TotalTopos

variable [HasSheafify (overSiteTotalTopology (J.over X) K) (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
  (totalForget K).op.HasPointwiseRightKanExtension P]

/- The total geometric morphism is induced by total localization into C/X. -/
#check (CategoryTheory.SemiRepresentableFamily.totalLocalization (J.over X) K :
  MorphismOfTopoiIn (J.over X) (overSiteTotalTopology (J.over X) K))

section Comparison

variable [HasWeakSheafify (J.over X) (Type (max w u v))]

/- Continuous restriction identifies with the geometric inverse image. -/
#check (CategoryTheory.Functor.CocontinuousPullback.comparisonIso (totalForget K)
    (overSiteTotalTopology (J.over X) K) (J.over X) :
  (totalForget K).sheafPullbackCocontinuous (Type (max w u v))
      (overSiteTotalTopology (J.over X) K) (J.over X) ≅
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
      (overSiteTotalTopology (J.over X) K) (J.over X))

end Comparison

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
  (augmentationTotalForget K).op.HasPointwiseRightKanExtension P]

/- The total augmentation comparison and its inverse-image mate apply over X. -/
#check (CategoryTheory.SemiRepresentableFamily.totalTopos_iso_totalLocalization
    (J.over X) K :
  (totalTopos (J.over X) K).pushforward ≅ (totalLocalization (J.over X) K).pushforward)
#check (CategoryTheory.SemiRepresentableFamily.totalTopos_inverseImage_iso_totalLocalization
    (J.over X) K :
  (totalTopos (J.over X) K).inverseImage ≅ (totalLocalization (J.over X) K).inverseImage)

end TotalTopos

section StageTopos

variable [∀ n : SimplexCategoryᵒᵖ,
  HasSheafify (overTopology (J.over X) (K.obj n)) (Type (max w u v))]
variable [∀ (n : SimplexCategoryᵒᵖ)
    (P : (OverSite (K.obj n))ᵒᵖ ⥤ Type (max w u v)),
  (forget (K.obj n)).op.HasPointwiseRightKanExtension P]

/- Every stage has its geometric localization morphism into the slice topos. -/
#check (CategoryTheory.SemiRepresentableFamily.localizationMorphism (J.over X) (K.obj n) :
  MorphismOfTopoiIn (J.over X) (overTopology (J.over X) (K.obj n)))

variable [∀ (n : SimplexCategory)
    (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type (max w u v)),
  (stageForget K n).op.HasPointwiseRightKanExtension P]

/- The stage augmentation comparisons and their inverse-image mates apply over X. -/
#check (CategoryTheory.SemiRepresentableFamily.stageTopos_iso_localizationMorphism
    (J.over X) K :
  ∀ n : SimplexCategory,
    (stageTopos (J.over X) K n).pushforward ≅
      (localizationMorphism (J.over X) (K.obj (op n))).pushforward)
#check (CategoryTheory.SemiRepresentableFamily.stageTopos_inverseImage_iso_localizationMorphism
    (J.over X) K :
  ∀ n : SimplexCategory,
    (stageTopos (J.over X) K n).inverseImage ≅
      (localizationMorphism (J.over X) (K.obj (op n))).inverseImage)

end StageTopos

section Sets

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
  (totalForget K).op.HasLeftKanExtension P]
variable [HasWeakSheafify (J.over X) (Type (max w u v))]

/- Lower shriek on sets goes from total sheaves to slice sheaves. -/
#check (CategoryTheory.Functor.sheafPullback (totalForget K) (Type (max w u v))
    (overSiteTotalTopology (J.over X) K) (J.over X) :
  Sheaf (overSiteTotalTopology (J.over X) K) (Type (max w u v)) ⥤
    Sheaf (J.over X) (Type (max w u v)))
#check (CategoryTheory.Functor.sheafAdjunctionContinuous (totalForget K)
    (Type (max w u v)) (overSiteTotalTopology (J.over X) K) (J.over X) :
  (totalForget K).sheafPullback (Type (max w u v))
      (overSiteTotalTopology (J.over X) K) (J.over X) ⊣
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
      (overSiteTotalTopology (J.over X) K) (J.over X))

end Sets

section Abelian

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
  (totalForget K).op.HasLeftKanExtension P]
variable [HasWeakSheafify (J.over X) AddCommGrpCat.{max w u v}]

/- Lower shriek on abelian groups is likewise left adjoint to restriction. -/
#check (CategoryTheory.Functor.sheafPullback (totalForget K) AddCommGrpCat.{max w u v}
    (overSiteTotalTopology (J.over X) K) (J.over X) :
  Sheaf (overSiteTotalTopology (J.over X) K) AddCommGrpCat.{max w u v} ⥤
    Sheaf (J.over X) AddCommGrpCat.{max w u v})
#check (CategoryTheory.Functor.sheafAdjunctionContinuous (totalForget K)
    AddCommGrpCat.{max w u v} (overSiteTotalTopology (J.over X) K) (J.over X) :
  (totalForget K).sheafPullback AddCommGrpCat.{max w u v}
      (overSiteTotalTopology (J.over X) K) (J.over X) ⊣
    (totalForget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
      (overSiteTotalTopology (J.over X) K) (J.over X))

end Abelian

/- Total inverse image restricts degreewise to stage inverse image over X. -/
#check (CategoryTheory.SemiRepresentableFamily.sheafInverseImage_fiberRestrict (J.over X) K :
  ∀ n : SimplexCategory,
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
        (overSiteTotalTopology (J.over X) K) (J.over X) ⋙
        sheafFiberRestrict (J.over X) K n ≅ sheafStageRestrict (J.over X) K n)

section AbelianEqualizer

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
  (totalForget K).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory)
    (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory)
    (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (i : Fin 2)
    (P : (OverSite (K.obj (op ⦋1⦌)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (overSiteFace K i).op.HasPointwiseRightKanExtension P]
variable [∀ (i : Fin 2)
    (P : (OverSite (K.obj (op ⦋1⦌)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (overSiteFace K i ⋙ forget (K.obj (op ⦋0⦌))).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf (J.over X) AddCommGrpCat.{max w u v})]

/- Abelian direct image over X is the canonical equalizer of the coface maps. -/
#check (CategoryTheory.SemiRepresentableFamily.abelianPushforwardToEqualizer_isIso
    (J.over X) K :
  ∀ G : Sheaf (overSiteTotalTopology (J.over X) K) AddCommGrpCat.{max w u v},
    IsIso (abelianPushforwardToEqualizer (J.over X) K G))

end AbelianEqualizer

/- Objectwise cohomology agrees with cohomology of the restricted component over X. -/
#check (CategoryTheory.SemiRepresentableFamily.cohomologyOverObject_component_iso
    (J.over X) K :
  ∀ (n : SimplexCategory) (i : (K.obj (op n)).I)
    (U : overSlice (K.obj (op n)) i)
    (F : Sheaf (overSiteTotalTopology (J.over X) K) AddCommGrpCat.{max w u v}) (p : ℕ),
    [HasSheafify (overSiteTotalTopology (J.over X) K) AddCommGrpCat.{max w u v}] →
    [HasExt.{z} (Sheaf (overSiteTotalTopology (J.over X) K) AddCommGrpCat.{max w u v})] →
    [HasSheafify ((J.over X).over ((K.obj (op n)).obj i)) AddCommGrpCat.{max w u v}] →
    [HasExt.{z} (Sheaf ((J.over X).over ((K.obj (op n)).obj i))
      AddCommGrpCat.{max w u v})] →
    IsIsomorphic
      (Sheaf.cohomologyOverObject.{z, 0} F
        ((Grothendieck.ι (overSiteDiagram K) (op n)).obj
          ((overIncl (K.obj (op n)) i).obj U)) p)
      (Sheaf.cohomologyOverObject.{z, max w u v}
        ((abelianComponentRestrict (J.over X) (K.obj (op n)) i).obj
          (((Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous
              AddCommGrpCat.{max w u v} (overTopology (J.over X) (K.obj (op n)))
              (overSiteTotalTopology (J.over X) K)).obj F)) U p))
