module

public import stacks_project.Chap90.Remark_90_7_10_Adjunction
public import stacks_project.Chap90.Remark_90_7_10_Functors
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.10: completion and restriction on cofibered sets are adjoint in the
usual categorical sense. We use the covariant set-valued functor presentation of
cofibered sets, as in the source's identification with the image of the discrete
realization functor. Restriction is left adjoint to completion. -/
@[stacks 06HB] #check (CategoryTheory.Functor.typesCompletionAdjunction :
  (Functor.typesRestrictInclusion :
    (CompleteLocalAlgCat Λ k ⥤ Type w) ⥤ (ArtinianLocalAlgCat Λ k ⥤ Type w)) ⊣
  (Functor.typesCompletionFunctor :
    (ArtinianLocalAlgCat Λ k ⥤ Type w) ⥤ (CompleteLocalAlgCat Λ k ⥤ Type w)))

/- The functorial hom-set bijection has restriction in its source and completion
in its target. -/
#check (CategoryTheory.Functor.typesCompletionHomEquiv :
  ∀ (G : CompleteLocalAlgCat Λ k ⥤ Type w) (F : ArtinianLocalAlgCat Λ k ⥤ Type w),
    (Functor.typesRestrictInclusion.obj G ⟶ F) ≃
      (G ⟶ Functor.typesCompletionFunctor.obj F))

/- The canonical map from restriction of completion to the original functor is
an isomorphism. -/
#check (CategoryTheory.Functor.typesCompletionCounitIso :
  Functor.typesCompletionFunctor ⋙ Functor.typesRestrictInclusion ≅
    𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w))

section CofiberedSets

variable {C : Type u} [Category.{v} C]

/- CofSet(C) is presented by covariant set-valued functors. Their discrete
realization in cofibered groupoids is fully faithful, and the source identifies
the functor category with its image. -/
#check (CategoryTheory.Functor.ofTypeValuedFunctor :
  (C ⥤ Type w) ⥤ CofiberedCategoryOver.Groupoids.{u, v, max u w, v} C)

#check (CategoryTheory.Functor.ofTypeValuedMap.bijective :
  ∀ {F G : C ⥤ Type w}, Function.Bijective
    (Functor.ofTypeValuedMap : (F ⟶ G) →
      (Functor.ofTypeValued F ⟶ Functor.ofTypeValued G)))

end CofiberedSets
