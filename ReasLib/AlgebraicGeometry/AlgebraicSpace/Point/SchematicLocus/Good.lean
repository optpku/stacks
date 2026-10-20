/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Good
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.Decent

/-!
# Dense open schemes in good algebraic spaces

An algebraic space quasi-separated and locally of finite type over a
quasi-separated algebraic space has a dense open subspace representable by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space quasi-separated and locally of finite type over a
quasi-separated algebraic space contains a dense open subspace representable by a scheme. -/
theorem exists_dense_open_isScheme_of_good {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ Dense U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
