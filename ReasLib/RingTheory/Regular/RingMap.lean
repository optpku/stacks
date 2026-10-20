/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.RingTheory.RingHom.Fiber.Map

@[expose] public section

/-!
# Regular Ring Maps

This module owns regularity for an explicit homomorphism of commutative rings.  The
definition combines flatness with geometric regularity of every residue-field fiber.

@stack 07BZ
-/

namespace RingHom

universe u v

/-- A ring map `f : R →+* S` is regular when it is flat and every fiber
`κ(p) ⊗[R] S` is geometrically regular over the residue field `κ(p)`. -/
@[stacks 07BZ "regular ring map"]
class Regular {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    Prop extends f.Flat where
  /-- The fiber over every prime of the source is geometrically regular over its residue field. -/
  isGeometricallyRegular_fiber (p : PrimeSpectrum R) :
    Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (f.Fiber p.asIdeal)

attribute [instance] Regular.isGeometricallyRegular_fiber

namespace Regular

/-- Unfold a regular ring map into flatness and geometric regularity of all its fibers. -/
@[stacks 07BZ "regular ring map characterization"]
theorem iff_flat_and_geometricallyRegular_fiber
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Regular ↔ f.Flat ∧ ∀ p : PrimeSpectrum R,
      Algebra.IsGeometricallyRegular p.asIdeal.ResidueField (f.Fiber p.asIdeal) := sorry

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}

namespace Fiber

/-- Every fiber of a regular ring map is a regular ring. -/
@[stacks 07BZ "regularity of fibers"]
instance instIsRegularRing (p : PrimeSpectrum R) [h : f.Regular] :
    IsRegularRing (f.Fiber p.asIdeal) := sorry

end Fiber

/-- The fiber of a regular ring map over any source prime is a regular ring. -/
@[stacks 07BZ "explicit regularity proof for a fiber"]
theorem isRegularRing_fiber (h : f.Regular) (p : PrimeSpectrum R) :
    IsRegularRing (f.Fiber p.asIdeal) := sorry

end

end Regular

end RingHom
