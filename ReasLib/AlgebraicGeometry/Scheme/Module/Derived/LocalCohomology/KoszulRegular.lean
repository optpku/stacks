module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.KoszulRegular
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubset.KoszulRegular
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Derived

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.ModuleDerived
open SheafOfModules.ClosedSubset.SupportedDerived

noncomputable section

universe u

/-- For a flat quasicoherent module on a scheme, the local-cohomology sheaves supported on a
Koszul-regular cutout of length `c` vanish in every degree other than `c`. -/
theorem AlgebraicGeometry.ClosedSubset.IsKoszulRegularCutout.localCohomologySheaf_isZero
    (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X) (c : ℕ)
    (hZ : AlgebraicGeometry.ClosedSubset.IsKoszulRegularCutout Z c) (ℱ : X.Modules)
    [ℱ.IsFlat] [ℱ.IsQuasicoherent] (i : ℤ) (hi : i ≠ (c : ℤ)) :
    IsZero
      (cohomologySheaf
        ((coreflector X.toRingedSpace.ringCatSheaf Z ⋙
            inclusion X.toRingedSpace.ringCatSheaf Z).obj
          ((ModuleCech.moduleToDerived X).obj ℱ)) i) := sorry

end
