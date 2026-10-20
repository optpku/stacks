/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.RingTheory.Flat.Fiber.Reduced

/-!
# Reduced Smooth Algebras

This leaf records reducedness of a smooth algebra over a reduced base ring.
-/

@[expose] public section

namespace Algebra.Smooth

universe u v

/-- A smooth algebra over a reduced commutative ring is reduced. -/
@[stacks 033B]
theorem isReduced_of_reduced
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] [IsReduced R] :
    IsReduced S := sorry

end Algebra.Smooth
