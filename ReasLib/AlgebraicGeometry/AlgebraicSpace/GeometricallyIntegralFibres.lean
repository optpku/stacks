/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral

/-!
# Morphisms with integral geometric fibres

A morphism of algebraic spaces has integral geometric fibres when the fibre over
every geometric point of its target is integral.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A morphism of algebraic spaces has integral geometric fibres if the fibre over
every geometric point of the target is integral. -/
@[mk_iff]
class HasIntegralGeometricFibres {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The geometric fibre over every geometric point of the target is integral. -/
  isIntegral_geometricFiber (ybar : GeometricPoint Y) :
    IsIntegral (fieldFiber f ybar.toFieldValuedPoint)

/-- The identity morphism of an algebraic space has integral geometric fibres. -/
instance instHasIntegralGeometricFibres_id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    HasIntegralGeometricFibres (𝟙 X) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
