/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.KrullDimension.Fiber.Valuation
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# Fibers over spectra of valuation rings

This leaf records equidimensionality and dimension comparison for the special
and generic fibers of a locally finite-type surjective morphism from an
irreducible scheme to the spectrum of a valuation ring.
-/

@[expose] public section

open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] {X : Scheme.{u}}

/-- The special fiber of a locally finite-type surjective morphism from an irreducible scheme
to the spectrum of a valuation ring is equidimensional. -/
theorem specialFiber_equidimensional
    (f : X ⟶ Spec (CommRingCat.of R)) [IrreducibleSpace X] [LocallyOfFiniteType f] [Surjective f] :
    EquidimensionalSpace (Scheme.Hom.fiber f (IsLocalRing.closedPoint R)) := sorry

/-- The special and generic fibers of a locally finite-type surjective morphism from an
irreducible scheme to the spectrum of a valuation ring have the same topological Krull
dimension. -/
theorem topologicalKrullDim_specialFiber_eq_genericFiber
    (f : X ⟶ Spec (CommRingCat.of R)) [IrreducibleSpace X] [LocallyOfFiniteType f] [Surjective f] :
    topologicalKrullDim (Scheme.Hom.fiber f (IsLocalRing.closedPoint R)) =
      topologicalKrullDim (Scheme.Hom.fiber f (genericPoint (Spec (CommRingCat.of R)))) := sorry

end AlgebraicGeometry.Scheme.Hom
