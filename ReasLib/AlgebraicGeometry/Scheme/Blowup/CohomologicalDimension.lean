module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Ideal.LocalCohomology

/-- If every fibre of the blowup of the spectrum of a Noetherian ring in an ideal `I`
has dimension strictly less than `d`, then local cohomology with support in `I`
has dimension at most `d`. -/
theorem hasDimensionLE_of_blowup
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X' : Scheme.{u}} (b : X' ⟶ Spec (CommRingCat.of A))
    [IsBlowup b (Scheme.idealSheafDataOfIdealOnSpec I)] (d : ℕ)
    (hdim : ∀ x : Spec (CommRingCat.of A),
      b.fiberDimension x < (d : WithBot ℕ∞)) :
    HasDimensionLE I (d : ℤ) := sorry

end Ideal.LocalCohomology
