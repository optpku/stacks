module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Derived

/-!
# Bounded-below derived adjunction of a Zariski augmentation

The canonical augmentation-derived adjunction and its unit are supplied by the
shared simplicial sheaf API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject TopCat

universe u

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)
variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(augmentationPushforward a).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))]

#check (CategoryTheory.SimplicialObject.plusDerivedAdjunction a :
  plusInverseImageDerived a ⊣ plusDirectImageDerived a)

#check (CategoryTheory.SimplicialObject.plusDerivedUnit a :
  𝟭 (DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) ⟶
    plusInverseImageDerived a ⋙ plusDirectImageDerived a)
