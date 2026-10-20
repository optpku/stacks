/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Standard precoverages of algebraic spaces

This module packages `0`-hypercover covers of algebraic spaces and the five
standard topologies as precoverages on `AlgebraicSpace S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A cover of an algebraic space in a precoverage is a `0`-hypercover. -/
abbrev Cover {S : Scheme.{u}} (K : Precoverage (AlgebraicSpace S)) :=
  Precoverage.ZeroHypercover.{u} K

/-- The underlying presieve of a cover belongs to the precoverage. -/
theorem cover_presieve_mem {S : Scheme.{u}} {K : Precoverage (AlgebraicSpace S)}
    {X : AlgebraicSpace S} (U : X.Cover K) : U.presieve₀ ∈ K X := sorry

/-- The algebraic-space precoverage associated to a standard topology. -/
def standardPrecoverage (S : Scheme.{u}) (τ : StandardTopology) :
    Precoverage (AlgebraicSpace S) :=
  match τ with
  | .zariski => zariskiPrecoverage S
  | .etale => etalePrecoverage
  | .smooth => precoverage (@Smooth S)
  | .syntomic => precoverage (@Syntomic S)
  | .fppf => fppfPrecoverage S

/-- The Zariski case of `standardPrecoverage` is the Zariski precoverage. -/
theorem standardPrecoverage_zariski (S : Scheme.{u}) :
    standardPrecoverage S .zariski = zariskiPrecoverage S := sorry

/-- The étale case of `standardPrecoverage` is the étale precoverage. -/
theorem standardPrecoverage_etale (S : Scheme.{u}) :
    standardPrecoverage S .etale = etalePrecoverage := sorry

/-- The smooth case of `standardPrecoverage` is the jointly surjective smooth
precoverage. -/
theorem standardPrecoverage_smooth (S : Scheme.{u}) :
    standardPrecoverage S .smooth = precoverage (@Smooth S) := sorry

/-- The syntomic case of `standardPrecoverage` is the jointly surjective syntomic
precoverage. -/
theorem standardPrecoverage_syntomic (S : Scheme.{u}) :
    standardPrecoverage S .syntomic = precoverage (@Syntomic S) := sorry

/-- The fppf case of `standardPrecoverage` is the fppf precoverage. -/
theorem standardPrecoverage_fppf (S : Scheme.{u}) :
    standardPrecoverage S .fppf = fppfPrecoverage S := sorry

end AlgebraicGeometry.AlgebraicSpace
