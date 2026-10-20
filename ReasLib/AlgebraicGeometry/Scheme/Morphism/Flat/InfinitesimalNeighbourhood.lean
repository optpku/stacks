/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood
public import ReasLib.RingTheory.Flatness.QuotientPowers.LocalCriterion

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

/-- A morphism between locally Noetherian schemes is flat at every point above a closed
subscheme if all its pullbacks to the infinitesimal neighbourhoods are flat. -/
@[stacks 0D4G]
theorem flatAt_of_flat_pullbacks {X S Z : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (f : X ⟶ S) (i : Z ⟶ S) [IsClosedImmersion i]
    [hflat : ∀ n : ℕ, Flat (pullback.snd f (toAmbient i n))]
    (x : X) (hx : f x ∈ Set.range i) :
    f.flatAt x := sorry

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
