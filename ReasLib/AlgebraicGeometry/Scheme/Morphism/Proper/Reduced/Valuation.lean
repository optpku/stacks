/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.Algebra.Module.ContentIdeal.ValuationRing
public import ReasLib.RingTheory.Valuation.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper flat scheme over the spectrum of a valuation ring is reduced if its special
fibre is reduced. -/
@[stacks 0H2T]
theorem isReduced_of_proper_flat_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    IsReduced X := sorry

/-- Every fibre of a proper flat scheme over the spectrum of a valuation ring is reduced if
its special fibre is reduced. -/
@[stacks 0H2T]
theorem isReduced_fiber_of_proper_flat_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))]
    (s : Spec (CommRingCat.of R)) :
    IsReduced (f.fiber s) := sorry

end AlgebraicGeometry.Scheme.Hom
