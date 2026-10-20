/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular

/-!
# Regularity via étale local rings

A locally Noetherian algebraic space is regular if and only if every étale local ring
at a geometric point is a regular local ring.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally Noetherian algebraic space is regular if and only if its étale local ring
at every geometric point is a regular local ring. -/
theorem isRegular_iff_forall_etaleLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] :
    IsRegular X ↔ ∀ xbar : GeometricPoint X, IsRegularLocalRing (etaleLocalRing X xbar) :=
  sorry

/-- The étale local ring of a regular locally Noetherian algebraic space at a geometric
point is a regular local ring. -/
instance etaleLocalRing.instIsRegularLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsRegular X] (xbar : GeometricPoint X) :
    IsRegularLocalRing (etaleLocalRing X xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
