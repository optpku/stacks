/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The generic fiber of a flat morphism from a connected scheme to the spectrum of a
discrete valuation ring is connected when its closed fiber is reduced. -/
@[stacks 055J]
instance connectedSpace_genericFiber_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [ConnectedSpace X]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    ConnectedSpace (f.fiber (genericPoint (Spec (CommRingCat.of R)))) := sorry

end AlgebraicGeometry.Scheme.Hom
