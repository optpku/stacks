/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- If a cohomology stalk of the new-upper-shriek dualizing object is nontrivial,
its degree is at least the negative local dimension of the fibre. -/
theorem neg_fiberDimension_le_of_cohomologyStalk_nontrivial
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) (x : X.obj.left) (d : ℕ)
    (h_dimension : fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : Nontrivial (cohomologyStalk (D.dualizingObject f) i x)) :
    -(d : ℤ) ≤ i := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
