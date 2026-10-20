module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber

/-!
# Morphisms with reduced geometric fibres

A morphism of algebraic spaces has reduced geometric fibres when the fibre over
every geometric point of its target is reduced.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A morphism of algebraic spaces has reduced geometric fibres if the fibre over
every geometric point of the target is reduced. -/
@[mk_iff]
class HasReducedGeometricFibres {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The geometric fibre over every geometric point of the target is reduced. -/
  isReduced_geometricFiber (ybar : GeometricPoint Y) :
    IsReduced (fieldFiber f ybar.toFieldValuedPoint)

namespace HasReducedGeometricFibres

/-- A morphism with reduced geometric fibres has a reduced geometric fibre over
every geometric point of the target. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasReducedGeometricFibres f] (ybar : GeometricPoint Y) :
    IsReduced (fieldFiber f ybar.toFieldValuedPoint) := sorry

/-- Reducedness of every geometric fibre witnesses that a morphism of algebraic
spaces has reduced geometric fibres. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ ybar : GeometricPoint Y,
      IsReduced (fieldFiber f ybar.toFieldValuedPoint)) :
    HasReducedGeometricFibres f := sorry

end HasReducedGeometricFibres

/-- The identity morphism of an algebraic space has reduced geometric fibres. -/
instance instHasReducedGeometricFibres_id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    HasReducedGeometricFibres (𝟙 X) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
