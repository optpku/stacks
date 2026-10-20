module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Cohomology.Subcategory

/-!
# Lemma 96.23.3

The inclusion of the selected full subcategory is fully faithful by
`CategoryTheory.ObjectProperty.fullyFaithfulι` and continuous and cocontinuous
by the four inclusion instances checked below. The canonical
`CategoryTheory.Functor.sheafAdjunctionCocontinuous` gives the corresponding
topos adjunction; its inverse image is restriction, constructed by
`CategoryTheory.Functor.sheafPushforwardContinuous`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe z w u

namespace AlgebraicGeometry.GroupoidsOver

#check (CategoryTheory.ObjectProperty.fullyFaithfulι :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (Q : ObjectProperty X.total),
    Q.ι.FullyFaithful)

#check (AlgebraicGeometry.GroupoidsOver.inclusion_isContinuous_etale :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))],
    Q.ι.IsContinuous (subcategoryTopology X StandardTopology.etale Q)
      X.etaleTopology)

#check (AlgebraicGeometry.GroupoidsOver.inclusion_isCocontinuous_etale :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))],
    Q.ι.IsCocontinuous (subcategoryTopology X StandardTopology.etale Q)
      X.etaleTopology)

#check (AlgebraicGeometry.GroupoidsOver.inclusion_isContinuous_fppf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))],
    Q.ι.IsContinuous (subcategoryTopology X StandardTopology.fppf Q)
      X.fppfTopology)

#check (AlgebraicGeometry.GroupoidsOver.inclusion_isCocontinuous_fppf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))],
    Q.ι.IsCocontinuous (subcategoryTopology X StandardTopology.fppf Q)
      X.fppfTopology)

/- Lemma 96.23.3: the étale case. -/
@[stacks 07AK] #check (AlgebraicGeometry.GroupoidsOver.cohomologySubcategoryEtale :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))]
    (h_atlas : ExistsSmoothSurjectiveObject Q)
    [HasSheafify X.etaleTopology AddCommGrpCat.{max w u}]
    [HasSheafify (subcategoryTopology X StandardTopology.etale Q)
      AddCommGrpCat.{max w u}]
    [HasExt.{z} (Sheaf X.etaleTopology AddCommGrpCat.{max w u})]
    [HasExt.{z}
      (Sheaf (subcategoryTopology X StandardTopology.etale Q)
        AddCommGrpCat.{max w u})]
    (F : Sheaf X.etaleTopology AddCommGrpCat.{max w u}) (p : ℕ),
    IsIsomorphic
      ((Sheaf.functorH (subcategoryTopology X StandardTopology.etale Q) p).obj
        ((Q.ι.sheafPushforwardContinuous AddCommGrpCat.{max w u}
            (subcategoryTopology X StandardTopology.etale Q)
            X.etaleTopology).obj F))
      ((Sheaf.functorH X.etaleTopology p).obj F))

/- Lemma 96.23.3: the fppf case. -/
@[stacks 07AK] #check (AlgebraicGeometry.GroupoidsOver.cohomologySubcategoryFppf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))]
    (h_atlas : ExistsSmoothSurjectiveObject Q)
    [HasSheafify X.fppfTopology AddCommGrpCat.{max w u}]
    [HasSheafify (subcategoryTopology X StandardTopology.fppf Q)
      AddCommGrpCat.{max w u}]
    [HasExt.{z} (Sheaf X.fppfTopology AddCommGrpCat.{max w u})]
    [HasExt.{z}
      (Sheaf (subcategoryTopology X StandardTopology.fppf Q)
        AddCommGrpCat.{max w u})]
    (F : Sheaf X.fppfTopology AddCommGrpCat.{max w u}) (p : ℕ),
    IsIsomorphic
      ((Sheaf.functorH (subcategoryTopology X StandardTopology.fppf Q) p).obj
        ((Q.ι.sheafPushforwardContinuous AddCommGrpCat.{max w u}
            (subcategoryTopology X StandardTopology.fppf Q)
            X.fppfTopology).obj F))
      ((Sheaf.functorH X.fppfTopology p).obj F))

end AlgebraicGeometry.GroupoidsOver
