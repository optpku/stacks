/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Fiber.Serre
public import ReasLib.RingTheory.RingHom.Fiber.Basic

/-!
# Reducedness Along Flat Maps

Reducedness ascends through a flat algebra when it holds on the base and on
all canonical residue-field fibers.
-/

@[expose] public section

namespace Algebra.Fiber

universe u v

/-- A flat algebra over a reduced Noetherian ring is reduced if all of its
residue-field fibers are reduced. -/
@[stacks 0C21]
theorem isReduced_of_flat
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsReduced R]
    (hfiber : (algebraMap R S).HasReducedFibers) :
    IsReduced S := sorry

end Algebra.Fiber
