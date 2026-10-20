module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.RingTheory.CohenMacaulay.Fiber.BaseChange

/-!
# The Cohen--Macaulay locus of a scheme morphism

This module defines the pointwise Cohen--Macaulay locus of a scheme morphism
and records its fibre-stalk characterization, openness, fibrewise density, and
compatibility with arbitrary base change.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The locus where a scheme morphism is Cohen--Macaulay at a point. -/
def cohenMacaulayLocus {X S : Scheme.{u}} (f : X ⟶ S) : Set X :=
  {x | f.CohenMacaulayAt x}

/-- A point lies in the Cohen--Macaulay locus exactly when the morphism is
Cohen--Macaulay at that point. -/
theorem mem_cohenMacaulayLocus {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    x ∈ f.cohenMacaulayLocus ↔ f.CohenMacaulayAt x := sorry

/-- For a flat, locally finitely presented morphism, the Cohen--Macaulay locus
is the locus where the local ring of the fibre is Cohen--Macaulay. -/
@[stacks 045U]
theorem cohenMacaulayLocus_eq_fiberStalk
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    f.cohenMacaulayLocus =
      {x : X | CohenMacaulayRing (fiberStalkAt f x)} := sorry

/-- The Cohen--Macaulay locus of a flat, locally finitely presented morphism
is open. -/
@[stacks 045U]
theorem isOpen_cohenMacaulayLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen f.cohenMacaulayLocus := sorry

/-- The Cohen--Macaulay locus of a flat, locally finitely presented morphism
is dense in every scheme-theoretic fibre. -/
@[stacks 045U]
theorem dense_cohenMacaulayLocus_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (s : S) :
    Dense ((f.fiberι s) ⁻¹' f.cohenMacaulayLocus) := sorry

/-- The Cohen--Macaulay locus of a flat, locally finitely presented morphism
commutes with arbitrary base change. -/
@[stacks 045U]
theorem cohenMacaulayLocus_eq_preimage_of_isPullback
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hcart : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f] :
    f'.cohenMacaulayLocus = g' ⁻¹' f.cohenMacaulayLocus := sorry

end AlgebraicGeometry.Scheme.Hom
