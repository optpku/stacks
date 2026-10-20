module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.DimensionFunction
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.EssentiallyFiniteType
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.MinimalPrime
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.ResidueField
public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.KrullDimension.Finite
public import ReasLib.Topology.Specialization.Dimension.Catenary

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- A Noetherian commutative ring admitting a dualizing complex is universally catenary. -/
theorem universallyCatenaryRing
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    {ω : DerivedCategory (ModuleCat.{u} A)} (hω : ω.IsDualizingComplex H) :
    UniversallyCatenaryRing.{u, u} A := sorry

/-- A Noetherian commutative ring admitting a dualizing complex has finite Krull dimension. -/
theorem finiteRingKrullDim
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    {ω : DerivedCategory (ModuleCat.{u} A)} (hω : ω.IsDualizingComplex H) :
    FiniteRingKrullDim A := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
