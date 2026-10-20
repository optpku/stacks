module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/-!
# Compatibility checks for connected geometric fibres

The connected-geometric-fibre property and its elementary API are provided by
its mathematical owner in `ReasLib`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

abbrev HasConnectedGeometricFibres {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop := AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres f

#check (AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
  (X ⟶ Y) → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.hasConnectedGeometricFibres_iff : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  (f : X ⟶ Y), AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres f ↔
    ∀ ybar : GeometricPoint Y,
      ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)))
#check (AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres.spec : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  (f : X ⟶ Y), ∀ (_ : AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres f),
    ∀ ybar : GeometricPoint Y,
      ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)))
#check (AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres.of : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
  {f : X ⟶ Y},
    (∀ ybar : GeometricPoint Y,
      ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint))) →
    AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres f)
#check (AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres.id : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
  AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (𝟙 X))

end Hom

end AlgebraicGeometry.AlgebraicSpace
