/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Constructibility on quasi-separated algebraic spaces

Étale-local constructibility agrees with local constructibility in the canonical
topology on the points of a quasi-separated algebraic space.
-/

@[expose] public section

open AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A subset of the points of a quasi-separated algebraic space is étale locally
constructible if and only if it is locally constructible in the canonical topology. -/
theorem isEtaleLocallyConstructible_iff_isLocallyConstructible
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (E : Set (Points X)) :
    IsEtaleLocallyConstructible E ↔ IsLocallyConstructible E :=
  sorry

/-- On a quasi-separated algebraic space, an étale locally constructible subset of the
points is locally constructible in the canonical topology. -/
theorem isLocallyConstructible_of_isEtaleLocallyConstructible
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (E : Set (Points X)) :
    IsEtaleLocallyConstructible E → IsLocallyConstructible E :=
  (isEtaleLocallyConstructible_iff_isLocallyConstructible E).mp

/-- On a quasi-separated algebraic space, a locally constructible subset of the points
in the canonical topology is étale locally constructible. -/
theorem isEtaleLocallyConstructible_of_isLocallyConstructible
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (E : Set (Points X)) :
    IsLocallyConstructible E → IsEtaleLocallyConstructible E :=
  (isEtaleLocallyConstructible_iff_isLocallyConstructible E).mpr

end AlgebraicGeometry.AlgebraicSpace
