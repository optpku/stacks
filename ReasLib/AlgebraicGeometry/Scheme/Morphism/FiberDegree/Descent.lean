/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree

/-!
# Descent of fibre-degree bounds

This file establishes cancellation of uniform fibre-degree bounds along flat
surjective precomposition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- A fixed bound on the fibre degrees of a composite also bounds its second factor when the
first factor is flat and surjective. -/
theorem degreesOfFibresBoundedBy_of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) [Flat f] [Surjective f] {n : ℕ}
    (hfh : degreesOfFibresBoundedBy (f ≫ h) n) :
    degreesOfFibresBoundedBy h n := sorry

/-- Universal boundedness of fibre degrees descends through flat surjective precomposition. -/
theorem universallyBoundedFibres_of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) [Flat f] [Surjective f]
    (hfh : universallyBoundedFibres (f ≫ h)) :
    universallyBoundedFibres h := sorry

end Scheme.Hom
end AlgebraicGeometry
