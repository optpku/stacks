/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Hilbert
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Hilbert cycle classes over discrete valuation rings

The Hilbert cycle-class homomorphism is surjective for finite-type scheme
morphisms to the spectrum of a discrete valuation ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- For a finite-type scheme morphism to the spectrum of a discrete valuation
ring, the Hilbert cycle-class homomorphism onto relative cycles is surjective
in every nonnegative dimension. -/
theorem cycleClassHomToGroup_surjective
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [f.FiniteType] (r : ℕ) :
    Function.Surjective (cycleClassHomToGroup f r) := sorry

/-- Every relative cycle family for a finite-type scheme morphism to the
spectrum of a discrete valuation ring lies in the image of the Hilbert
cycle-class homomorphism. -/
theorem mem_range_cycleClassHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [f.FiniteType] (r : ℕ)
    {α : f.FiberCycleFamily r} (hα : IsRelative α) :
    α ∈ Set.range (cycleClassHom f r) := sorry

end AlgebraicGeometry.RelativeCycle
