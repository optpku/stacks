/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Dimension along locally quasi-finite morphisms

A locally quasi-finite morphism of algebraic spaces cannot increase the
dimension of the local ring at a point or the global dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The local-ring dimension at a point of an algebraic space is at most the
local-ring dimension at its image under a locally quasi-finite morphism. -/
theorem localRingDimAt_le_of_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : Points X) :
    localRingDimAt x ≤ localRingDimAt (Points.map f x) :=
  sorry

/-- The dimension of an algebraic space is at most the dimension of the target
of a locally quasi-finite morphism. -/
@[stacks 0ED0]
theorem dimension_le_of_locallyQuasiFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyQuasiFinite f] :
    dimension X ≤ dimension Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
