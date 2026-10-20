/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgClosedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Surjectivity of locally finite type morphisms on algebraically closed points

A locally finite type morphism of algebraic spaces is surjective if and only
if it is surjective on algebraically closed field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type morphism of algebraic spaces over a scheme is
surjective if and only if postcomposition is surjective on points valued in
every algebraically closed field over the base scheme. -/
theorem surjective_iff_surjectiveOnAlgClosedPoints
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    Surjective f ↔ surjectiveOnAlgClosedPoints f :=
  sorry

namespace Surjective

/-- A locally finite type morphism of algebraic spaces that is surjective on
algebraically closed field-valued points is surjective. -/
theorem of_surjectiveOnAlgClosedPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [LocallyOfFiniteType f] (h : surjectiveOnAlgClosedPoints f) :
    Surjective f :=
  (surjective_iff_surjectiveOnAlgClosedPoints f).mpr h

end Surjective

namespace surjectiveOnAlgClosedPoints

/-- A locally finite type surjective morphism of algebraic spaces is
surjective on algebraically closed field-valued points. -/
theorem of_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Surjective f] :
    surjectiveOnAlgClosedPoints f :=
  (surjective_iff_surjectiveOnAlgClosedPoints f).mp inferInstance

end surjectiveOnAlgClosedPoints

end AlgebraicGeometry.AlgebraicSpace
