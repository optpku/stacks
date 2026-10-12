/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent

/-!
# Reducedness of proper schemes over discrete valuation rings

This file gives a reducedness criterion for a proper scheme over a discrete valuation ring in
terms of its irreducible components and special fiber.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper scheme over a discrete valuation ring is reduced if all of its irreducible
components dominate the base and its special fiber is reduced. -/
theorem isReduced_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hdominant : ∀ Z : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι Z ≫ f))
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    IsReduced X := sorry

/-- The generic fiber of a proper scheme over a discrete valuation ring is reduced if all
irreducible components dominate the base and the special fiber is reduced. -/
theorem isReduced_genericFiber_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hdominant : ∀ Z : irreducibleComponents X,
      IsDominant (X.irreducibleComponentSubschemeι Z ≫ f))
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    IsReduced (f.fiber (genericPoint (Spec (CommRingCat.of R)))) := sorry

end AlgebraicGeometry.Scheme.Hom
