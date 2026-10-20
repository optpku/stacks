/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Noetherian DVR criterion for proper morphisms of algebraic spaces

A finite-type quasi-separated morphism of algebraic spaces into a locally
Noetherian algebraic space is proper as soon as every DVR valuative square has
a unique lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

/-- A finite-type quasi-separated morphism of algebraic spaces over a scheme
with locally Noetherian target is proper if every DVR valuative square has a
unique lift. -/
instance of_dvr {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [FiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.DVR f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
