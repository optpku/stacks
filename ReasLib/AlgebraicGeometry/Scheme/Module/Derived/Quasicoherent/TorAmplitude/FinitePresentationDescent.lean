module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.FlatRepresentative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FlatStratification

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a surjective finite-presentation morphism `f : X ⟶ S` and a nonpositive
`M : DerivedQCoh S`, the underlying derived module of `M` has a flat representative
concentrated in degree zero exactly when its derived pullback along `f` does. -/
theorem hasFlatRepresentativeIn_zero_iff_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [Scheme.Hom.FinitePresentation f]
    (M : DerivedQCoh S) (hM : ((inclusion S).obj M).IsLE 0) :
    RingedSpace.ModuleDerived.HasFlatRepresentativeIn ((inclusion S).obj M) 0 0 ↔
      RingedSpace.ModuleDerived.HasFlatRepresentativeIn
        ((inclusion X).obj ((pullback f).obj M)) 0 0 := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
