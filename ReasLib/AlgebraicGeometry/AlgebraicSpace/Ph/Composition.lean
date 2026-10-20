module

public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Site
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Ph.Big

/-- The inverse image of the composite of big ph morphisms of topoi is
canonically isomorphic to the inverse image induced by the composite morphism
of algebraic spaces. -/
noncomputable def morphismOfTopoi_comp_inverseImageIso
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (MorphismOfTopoiIn.comp
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) g)
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f)).inverseImage ≅
        (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1}
          (phTopology S) (f ≫ g)).inverseImage :=
  (phTopology S).overMapPullbackComp (Type (u + 1)) f g

end AlgebraicGeometry.AlgebraicSpace.Ph.Big
