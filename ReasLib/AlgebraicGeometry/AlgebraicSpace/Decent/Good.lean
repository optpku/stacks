/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre

/-!
# Monomorphic field-valued points of good algebraic spaces

A quasi-separated algebraic space locally of finite type over a quasi-separated
algebraic space has a monomorphic field-valued representative at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every point of an algebraic space quasi-separated and locally of finite type
over a quasi-separated algebraic space is represented by a monomorphism from the
spectrum of a field. -/
theorem existsMono_fieldValuedPoint_of_good {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (x : Points X) : existsMonoFieldValuedPoint X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
