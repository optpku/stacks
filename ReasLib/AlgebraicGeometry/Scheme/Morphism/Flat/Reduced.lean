/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Reduced

@[expose] public section

universe u

namespace AlgebraicGeometry.Flat

/-- Reducedness descends along flat surjective morphisms of schemes. -/
@[stacks 06QM]
theorem isReduced_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := sorry

end AlgebraicGeometry.Flat
