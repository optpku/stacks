module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChangeComparison

/-! Compatibility checks for the small étale base-change comparison API. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

#check (smallEtaleBaseChangeHom f g f' g' h_cart F :
  (smallEtaleMorphismOfTopoi g).inverseImage.obj
      ((smallEtaleMorphismOfTopoi f).pushforward.obj F) ⟶
    (smallEtaleMorphismOfTopoi f').pushforward.obj
      ((smallEtaleMorphismOfTopoi g').inverseImage.obj F))

end AlgebraicGeometry.AlgebraicSpace
