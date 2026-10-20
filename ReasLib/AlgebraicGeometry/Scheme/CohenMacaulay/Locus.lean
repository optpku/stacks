/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.RingTheory.CohenMacaulay.Module

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The Cohen-Macaulay locus of a locally Noetherian scheme is the set of points where the
local ring is Cohen-Macaulay as a module over itself. -/
def cohenMacaulayLocus (X : Scheme.{u}) [IsLocallyNoetherian X] : Set X :=
  {x | Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x)}

/-- Membership in the Cohen-Macaulay locus is the Cohen-Macaulay property of the local ring
viewed as a module over itself. -/
@[simp]
theorem mem_cohenMacaulayLocus (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    x ∈ X.cohenMacaulayLocus ↔
      Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
