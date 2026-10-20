module

public import ReasLib.CategoryTheory.Sites.Topos.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos

/-! Comparisons between inverse and direct image functors in cartesian squares
of algebraic spaces and on their small étale topoi. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
section
variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)

/-- The inverse-image identification associated to a cartesian square. -/
def smallEtaleInverseImageSquare :
    (smallEtaleMorphismOfTopoi g).inverseImage ⋙
        (smallEtaleMorphismOfTopoi f').inverseImage ≅
      (smallEtaleMorphismOfTopoi f).inverseImage ⋙
        (smallEtaleMorphismOfTopoi g').inverseImage :=
  (smallEtaleMorphismOfTopoiComp f' g).symm ≪≫
    eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
      h_cart.w.symm) ≪≫
    smallEtaleMorphismOfTopoiComp g' f

/-- The inverse-image square is given by the composition comparison and the
commutativity witness of the cartesian square. -/
theorem smallEtaleInverseImageSquare_eq :
    smallEtaleInverseImageSquare f g f' g' h_cart =
      (smallEtaleMorphismOfTopoiComp f' g).symm ≪≫
        eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
          h_cart.w.symm) ≪≫
        smallEtaleMorphismOfTopoiComp g' f := rfl

variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- The canonical Beck--Chevalley comparison on small étale sheaves. -/
def smallEtaleBaseChangeHom :
    (smallEtaleMorphismOfTopoi g).inverseImage.obj
      ((smallEtaleMorphismOfTopoi f).pushforward.obj F) ⟶
      (smallEtaleMorphismOfTopoi f').pushforward.obj
        ((smallEtaleMorphismOfTopoi g').inverseImage.obj F) :=
  (MorphismOfTopoiIn.baseChange (smallEtaleMorphismOfTopoi g')
      (smallEtaleMorphismOfTopoi f') (smallEtaleMorphismOfTopoi f)
      (smallEtaleMorphismOfTopoi g)
      (smallEtaleInverseImageSquare f g f' g' h_cart).hom).app F

/-- The canonical comparison is the objectwise Beck--Chevalley mate. -/
theorem smallEtaleBaseChangeHom_eq :
    smallEtaleBaseChangeHom f g f' g' h_cart F =
      (MorphismOfTopoiIn.baseChange (smallEtaleMorphismOfTopoi g')
          (smallEtaleMorphismOfTopoi f') (smallEtaleMorphismOfTopoi f)
          (smallEtaleMorphismOfTopoi g)
          (smallEtaleInverseImageSquare f g f' g' h_cart).hom).app F := rfl
end
section
variable {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y)
variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- The canonical comparison for the chosen fibre product of algebraic spaces. -/
def smallEtaleBaseChangeHom_pullback :
    (smallEtaleMorphismOfTopoi g).inverseImage.obj
      ((smallEtaleMorphismOfTopoi f).pushforward.obj F) ⟶
      (smallEtaleMorphismOfTopoi (pullback.fst g f)).pushforward.obj
        ((smallEtaleMorphismOfTopoi (pullback.snd g f)).inverseImage.obj F) :=
  smallEtaleBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
    (IsPullback.of_hasPullback g f).flip F

/-- The chosen-pullback comparison is the canonical comparison for its cartesian
square. -/
theorem smallEtaleBaseChangeHom_pullback_eq :
    smallEtaleBaseChangeHom_pullback f g F =
      smallEtaleBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip F := rfl
end
end AlgebraicGeometry.AlgebraicSpace
