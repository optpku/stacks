module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Big

/-- The inverse image of the composite of big étale morphisms of topoi is
canonically isomorphic to the inverse image induced by the composite morphism
of algebraic spaces. -/
noncomputable def morphismOfTopoi_comp_inverseImageIso
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f)).inverseImage ≅
      (morphismOfTopoi (f ≫ g)).inverseImage :=
  (AlgebraicGeometry.AlgebraicSpace.etaleTopology (S := S)).overMapPullbackComp
    (Type (u + 1)) f g

end AlgebraicGeometry.AlgebraicSpace.Etale.Big
