/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization

@[expose] public section

open scoped ENat

universe u v

namespace AlgebraicGeometry.PuncturedSpectrum

/-- The punctured spectrum of a Noetherian local ring of depth at least two is connected. -/
@[stacks 0BLR]
theorem connectedSpace_of_moduleDepth_ge_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) :
    ConnectedSpace (scheme A) := sorry

/-- The punctured spectrum of a henselization of a Noetherian local ring of depth at
least two is connected. -/
@[stacks 0BLR]
theorem connectedSpace_henselization_of_moduleDepth_ge_two
    (A : Type u) (Ah : Type v)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) :
    ConnectedSpace (scheme Ah) := sorry

/-- The punctured spectrum of a strict henselization of a Noetherian local ring of depth at
least two is connected. -/
@[stacks 0BLR]
theorem connectedSpace_strictHenselization_of_moduleDepth_ge_two
    (A : Type u) (Ash : Type v)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) :
    ConnectedSpace (scheme Ash) := sorry

end AlgebraicGeometry.PuncturedSpectrum
