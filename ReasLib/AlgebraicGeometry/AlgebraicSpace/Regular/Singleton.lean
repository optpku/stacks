/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Regularity of reduced locally Noetherian singleton algebraic spaces

A reduced, locally Noetherian algebraic space whose space of points is a
singleton is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsRegular

/-- A reduced, locally Noetherian algebraic space whose space of points is a
singleton is regular. -/
instance of_singleton_points {S : Scheme.{u}} (Z : AlgebraicSpace S)
    [IsReduced Z] [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    IsRegular Z := sorry

end IsRegular

end AlgebraicGeometry.AlgebraicSpace
