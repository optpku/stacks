module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.RingedComparison
public import stacks_project.Chap85.Lemma_85_34_1_Ringed

/-! # Fppf–étale comparison square of ringed topoi

The total comparisons and the genuine augmentations carry the canonical structure-sheaf maps.
The degree-zero cartesian section map is retained for its direct consumers.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open CategoryTheory.SimplicialObject

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.fppfEtaleRingedComparison :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)),
    RingedSite.ToposHom (fppfTotalRingedSite U) (etaleTotalRingedSite U))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.spacesEtaleAugmentationRinged :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))
    {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
    RingedSite.ToposHom (etaleTotalRingedSite U) (spacesRingedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.spacesEtaleAugmentationRinged_structureSheafMap :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))
    {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
    (spacesRingedSite X).structureSheaf ⟶
      ((augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).obj
          (etaleTotalRingedSite U).structureSheaf)
