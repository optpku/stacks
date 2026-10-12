/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper morphism from a scheme to the spectrum of a discrete valuation ring
with empty closed-point fibre has an empty source scheme. -/
theorem isEmpty_of_isEmpty_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hfiber : IsEmpty (f.fiber (IsLocalRing.closedPoint R))) :
    IsEmpty X := sorry

/-- For a commutative local ring, the fibre over the closed point of the spectrum
is empty exactly when the pullback along the residue-field morphism is empty. -/
theorem isEmpty_specialFiber_iff_isEmpty_pullback_residue
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    IsEmpty (f.fiber (IsLocalRing.closedPoint R)) ↔
      IsEmpty (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme) := sorry

end AlgebraicGeometry.Scheme.Hom
