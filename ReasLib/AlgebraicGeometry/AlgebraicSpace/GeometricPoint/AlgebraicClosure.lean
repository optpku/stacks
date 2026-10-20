/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-!
# Algebraic-closure representatives of algebraic-space points

Extending the source field of a field-valued point to its algebraic closure
produces a geometric point with the same image. Every point of an algebraic
space has a chosen geometric representative obtained by this construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricPoint

/-- The geometric point obtained by extending a field-valued point along the
algebraic closure of its source field. -/
noncomputable def extend {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : FieldValuedPoint X) : GeometricPoint X :=
  let f := AlgebraicGeometry.FieldExtension.specMap p.K (AlgebraicClosure p.K)
  of (AlgebraicClosure p.K) (f ≫ p.structureHom) (ofOverHomMk f rfl ≫ p.hom)

/-- The algebraic-closure extension of a field-valued point has image the class
of that point. -/
theorem extend_image {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : FieldValuedPoint X) : (extend p).image = Points.mk p :=
  sorry

end GeometricPoint

/-- A chosen geometric point of `Y` lying over `y`, obtained by algebraic closure
of a field-valued representative. -/
noncomputable def geometricPointOver {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (y : Points Y) : GeometricPoint Y :=
  GeometricPoint.extend (Quotient.out (y : Quotient (equivalentSetoid Y)))

/-- The chosen geometric point over `y` has image `y`. -/
theorem geometricPointOver_image {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (y : Points Y) : (geometricPointOver y).image = y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
