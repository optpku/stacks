/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.Etale.Neighborhood

@[expose] public section

/-!
# Completed local maps of etale neighborhoods

An etale neighborhood already contains the selected point and its lying-over
proof. This file packages the induced map of completed local rings so callers
only supply the neighborhood.
-/

universe u v

namespace PrimeSpectrum.EtaleNeighborhood

/-- The canonical map from the completed local ring at the base point to the
completed local ring at the selected point of an etale neighborhood. -/
@[stacks 0CAR "completed local map of an etale neighborhood"]
noncomputable abbrev completedLocalMap
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    CompletedLocalRing p →+* CompletedLocalRing U.point :=
  AdicCompletion.mapLocal
    (Localization.localRingHom p.asIdeal U.point.asIdeal
      (algebraMap R U.carrier) U.over)

/-- The structural algebra map from an etale neighborhood to the completed
local ring at its selected point. -/
@[stacks 0CAR "etale neighborhood map to the completed local ring"]
noncomputable abbrev toCompletedLocalRing
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    (U : EtaleNeighborhood.{u, v} p) :
    U.carrier →ₐ[R] CompletedLocalRing U.point :=
  IsScalarTower.toAlgHom R U.carrier (CompletedLocalRing U.point)

end PrimeSpectrum.EtaleNeighborhood
