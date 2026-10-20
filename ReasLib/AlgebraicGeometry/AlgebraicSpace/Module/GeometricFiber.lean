module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-!
# Geometric-fibre local rings and module stalks

A geometric point induces a geometric point of the fibre over its image, with the
same algebraically closed source field. The local ring and pulled-back module stalk
are taken on this fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The geometric point of the fibre over the image of `xbar`, induced by the
universal pullback lift and retaining the source field of `xbar`. -/
def geometricFiberPoint (f : X ⟶ Y) (xbar : GeometricPoint X) :
    GeometricPoint (fieldFiber f (xbar.map f).toFieldValuedPoint) where
  K := xbar.K
  field := xbar.field
  structureHom := xbar.structureHom
  hom := Limits.pullback.lift xbar.hom (𝟙 (ofOver xbar.overObj)) (by
    change xbar.hom ≫ f = 𝟙 (ofOver xbar.overObj) ≫ (xbar.hom ≫ f)
    exact (Category.id_comp _).symm)
  isAlgClosed := xbar.isAlgClosed

/-- The morphism of the induced geometric-fibre point is the universal pullback lift. -/
theorem geometricFiberPoint_hom (f : X ⟶ Y) (xbar : GeometricPoint X) :
    (geometricFiberPoint f xbar).hom =
      Limits.pullback.lift xbar.hom (𝟙 (ofOver xbar.overObj)) (by
        change xbar.hom ≫ f = 𝟙 (ofOver xbar.overObj) ≫ (xbar.hom ≫ f)
        exact (Category.id_comp _).symm) :=
  rfl

/-- The étale local ring of the geometric fibre at the induced geometric point. -/
abbrev geometricFiberRing (f : X ⟶ Y) (xbar : GeometricPoint X) :=
  etaleLocalRing (fieldFiber f (xbar.map f).toFieldValuedPoint)
    (geometricFiberPoint f xbar)

/-- The geometric-fibre ring is the étale local ring at the induced geometric point. -/
theorem geometricFiberRing_eq (f : X ⟶ Y) (xbar : GeometricPoint X) :
    geometricFiberRing f xbar =
      etaleLocalRing (fieldFiber f (xbar.map f).toFieldValuedPoint)
        (geometricFiberPoint f xbar) :=
  rfl

/-- The stalk at the induced geometric point of the module pulled back to the geometric fibre. -/
abbrev geometricFiberStalk (F : X.Modules) (f : X ⟶ Y) (xbar : GeometricPoint X) :=
  stalkModuleCat (geometricFiberPoint f xbar)
    ((pullback (fieldFiberι f (xbar.map f).toFieldValuedPoint)).obj F)

/-- The geometric-fibre stalk is the module stalk of the pullback along the fibre projection. -/
theorem geometricFiberStalk_eq (F : X.Modules) (f : X ⟶ Y) (xbar : GeometricPoint X) :
    geometricFiberStalk F f xbar =
      stalkModuleCat (geometricFiberPoint f xbar)
        ((pullback (fieldFiberι f (xbar.map f).toFieldValuedPoint)).obj F) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
