/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Fiber.Reduced

@[expose] public section

/-!
# Reducedness from Flat Maps with Reduced Fibers

@stack 0C21

This map-oriented leaf removes the incidental `Algebra` packaging from the
flat reducedness ascent theorem when the input is already an explicit ring
homomorphism.
-/

universe u v

namespace RingHom.HasReducedFibers

/-- Tag `0C21`: a flat map from a reduced Noetherian ring with reduced fibers
has reduced target. -/
@[stacks 0C21 "ring-hom formulation"]
theorem isReduced_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    [IsNoetherianRing R] [IsNoetherianRing S] [IsReduced R]
    (hflat : f.Flat) (hfiber : f.HasReducedFibers) :
    IsReduced S := sorry

end RingHom.HasReducedFibers
