module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.NormalizationDegree
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- A normalization-degree function of a dualizing complex is a dimension function on the
prime spectrum. -/
theorem isDimensionFunction
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    {ω : DerivedCategory (ModuleCat.{u} A)} (hω : ω.IsDualizingComplex H)
    {δ : PrimeSpectrum A → ℤ} (hδ : IsNormalizationDegreeFunction ω δ) :
    IsDimensionFunction δ := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
