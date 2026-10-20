module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Cohomology

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite TopologicalSpace TopCat

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
variable [∀ V : Opens X,
    HasSheafify (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}]
variable [∀ V : Opens X,
    HasExt.{u} (Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- The presheaf of cohomology groups on augmentation preimages and its associated sheaf. -/
#check (CategoryTheory.SimplicialObject.augmentationCohomologyPresheaf a :
  Sheaf (zariskiTopology Y) AddCommGrpCat.{u} → ℕ → (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
#check (CategoryTheory.SimplicialObject.sheafifiedAugmentationCohomology a :
  Sheaf (zariskiTopology Y) AddCommGrpCat.{u} → ℕ →
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

end CategoryTheory.SimplicialObject
