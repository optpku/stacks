/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped PrimeSpectrum

universe u

namespace Ideal

/-- Flat algebras with geometrically integral fibres carry prime ideals of the base to prime
ideals. -/
instance instIsPrimeMapOfFlatGeometricallyIntegral
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (p : PrimeSpectrum R) :
    (Ideal.map (algebraMap R S) p.asIdeal).IsPrime := sorry

end Ideal
