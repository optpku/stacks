/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Invertible modules over valuation rings

This module studies triviality of invertible modules in families of schemes over valuation rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace Scheme.Hom Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace Invertible

/-- An invertible module on a proper flat finitely presented scheme over a valuation ring is
trivial if its generic-fiber pullback is trivial, its special fiber is integral, and the canonical
map from the generic-point residue field to generic-fiber global functions is bijective. -/
@[stacks 0EX8]
theorem isTrivial_of_valuationRing
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [IsProper f] [FinitePresentation f]
    (L : X.Modules) [Invertible L]
    [IsIntegral (f.fiber (IsLocalRing.closedPoint R))]
    (h_generic_trivial :
      IsTrivial
        ((pullback
          (f.fiberι (genericPoint (Spec (CommRingCat.of R))))).obj L))
    (h_global_sections : Function.Bijective
      (globalSectionsMap
        (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R)))))) :
    IsTrivial L := sorry

end Invertible
end Modules
end Scheme
end AlgebraicGeometry
