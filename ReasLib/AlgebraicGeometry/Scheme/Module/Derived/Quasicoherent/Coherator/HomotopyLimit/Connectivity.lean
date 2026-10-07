module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.HomotopyLimit

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The coherator of an ambient homotopy limit of a sequential inverse system of
quasi-coherent sheaves has no cohomology in degrees below `0`. -/
theorem rightAdjoint_homotopyLimit_isGE_zero
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : HomotopyLimit.IsOf
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) K) :
    ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj.IsGE 0 := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
