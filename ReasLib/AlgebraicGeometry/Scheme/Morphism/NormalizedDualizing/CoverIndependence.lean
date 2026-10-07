module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Uniqueness

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace NormalizedDualizingComplexOnCover

/-- A normalized dualizing complex on one finite separated open cover induces normalized data on
another such cover with the same underlying complex. -/
theorem existsOnCoverWithSameComplex {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (coverU coverV : FiniteSeparatedOpenCover f)
    (dualityU : ExceptionalInverseImageSetup f coverU)
    (dualityV : ExceptionalInverseImageSetup f coverV)
    (K : NormalizedDualizingComplexOnCover f HS HX ωS hωS coverU dualityU) :
    ∃ K' : NormalizedDualizingComplexOnCover f HS HX ωS hωS coverV dualityV,
      K'.complex = K.complex := sorry

end NormalizedDualizingComplexOnCover
end Hom
end Scheme
end AlgebraicGeometry
