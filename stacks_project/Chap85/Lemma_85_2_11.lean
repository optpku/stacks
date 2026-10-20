module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor TopologicalSpace TopCat

universe u

/- Lemma 85.2.11: for an augmentation of a simplicial space and an abelian sheaf,
the higher direct image is the sheaf associated to the cohomology presheaf on
open preimages of the augmentation. -/
@[stacks 0D84] #check
  (CategoryTheory.SimplicialObject.sheafifiedAugmentationCohomology_iso_higherDirectImage :
    ∀ {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}}
      (a : Y ⟶ CategoryTheory.SimplicialObject.constSpace X)
      [HasSheafify (CategoryTheory.SimplicialObject.zariskiTopology Y) AddCommGrpCat.{u}]
      [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
      [∀ V : Opens X,
        HasSheafify (CategoryTheory.SimplicialObject.zariskiTopology
          (CategoryTheory.SimplicialObject.augmentationPreimage a V)) AddCommGrpCat.{u}]
      [∀ V : Opens X,
        HasExt.{u} (Sheaf (CategoryTheory.SimplicialObject.zariskiTopology
          (CategoryTheory.SimplicialObject.augmentationPreimage a V)) AddCommGrpCat.{u})]
      [∀ F : (CategoryTheory.SimplicialObject.zariskiSite
        (CategoryTheory.SimplicialObject.constSpace X))ᵒᵖ ⥤ AddCommGrpCat.{u},
        (CategoryTheory.SimplicialObject.constProjection X).op.HasPointwiseRightKanExtension F]
      [HasInjectiveResolutions
        (Sheaf (CategoryTheory.SimplicialObject.zariskiTopology Y) AddCommGrpCat.{u})]
      (F : Sheaf (CategoryTheory.SimplicialObject.zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ),
      CategoryTheory.SimplicialObject.sheafifiedAugmentationCohomology a F n ≅
        (CategoryTheory.SimplicialObject.augmentationHigherDirectImageFunctor a n).obj F)
