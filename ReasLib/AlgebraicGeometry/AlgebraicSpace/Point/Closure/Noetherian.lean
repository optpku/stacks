/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian

/-!
# Locally Noetherian reduced point closures
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PointClosure

/-- The reduced closure of a point of a locally Noetherian algebraic space is
locally Noetherian. -/
instance instIsLocallyNoetherian_space {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (x : Points X) : IsLocallyNoetherian (space x) :=
  IsLocallyNoetherian.of_isClosedImmersion (ι x)

end AlgebraicGeometry.AlgebraicSpace.PointClosure
