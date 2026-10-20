module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation

/-!
# Augmentation morphism compatibility

The augmentation morphism and its properties are provided by the shared simplicial
sheaf API. The constant inverse-image comparison retains its established name.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.SimplicialObject
open TopologicalSpace Opposite
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section
universe u

namespace CategoryTheory.SimplicialObject

/-- Constant-space geometric inverse image agrees with continuous precomposition. -/
def constInverseImageIso {X : TopCat.{u}} :
    (constMorphism X)⁻¹ ≅
      (constProjection X).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) :=
  constMorphism_inverseImage_iso X

end CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

#check (CategoryTheory.SimplicialObject.augmentationMorphism a :
  MorphismOfTopoiIn (Opens.grothendieckTopology X) (zariskiTopology Y))
