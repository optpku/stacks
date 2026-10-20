module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.Exact

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

#check (AlgebraicGeometry.Scheme.DerivedQCoh.inclusionRightAdjointCommShift :
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
    ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint).CommShift ℤ)

#check (AlgebraicGeometry.Scheme.DerivedQCoh.inclusionRightAdjointIsTriangulated :
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
    ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint).IsTriangulated)

end AlgebraicGeometry.Scheme.DerivedQCoh
