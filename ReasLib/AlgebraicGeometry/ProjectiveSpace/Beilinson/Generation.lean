module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.DerivedGenerator
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal

/-!
# Weak generation by the derived Beilinson generator

The degree-zero object on the finite coproduct of standard negative twisting sheaves weakly
generates the derived category of modules with quasicoherent cohomology on projective space.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- On standard projective space over a commutative ring, the degree-zero
Beilinson object is a weak generator of the derived category with quasicoherent cohomology. -/
theorem derivedBeilinsonGenerator_isWeakGenerator
    (A : Type u) [CommRing A] (n : ℕ) :
    IsWeakGenerator (derivedBeilinsonGenerator A n) := sorry

end AlgebraicGeometry.ProjectiveSpace
