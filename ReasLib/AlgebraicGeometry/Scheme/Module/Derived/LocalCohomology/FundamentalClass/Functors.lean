module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.ExteriorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open SheafOfModules.ClosedSubset
open SheafOfModules.RingedSite.ExteriorPower
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.LocalCohomology

variable {X Z : Scheme.{u}}

/-- The source functor
`ℱ ↦ i_* ((Λ[c] conormalSheaf i)ᘁ ⊗ i^*ℱ)` of the fundamental-class map. -/
noncomputable def sourceFunctor (i : Z ⟶ X) (c : ℕ) :
    Scheme.QCoh X ⥤ X.toRingedSpace.Modules :=
  Scheme.QCoh.inclusion X ⋙
    Scheme.Modules.pullback i ⋙
    MonoidalCategory.tensorLeft
      ((ihom (sheaf Z.𝒪 (Scheme.Hom.conormalSheaf i) c)).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ⋙
    Scheme.Modules.pushforward i ⋙
    Scheme.Modules.toRingedSpace X

/-- The degree-`c` local-cohomology functor on `X`, supported on the closed image of `i`. -/
noncomputable def functor (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ) :
    Scheme.QCoh X ⥤ X.toRingedSpace.Modules :=
  Scheme.QCoh.inclusion X ⋙
    ModuleCech.moduleToDerived X ⋙
    Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf i.ker.support ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.ClosedSubset.Modules X.toRingedSpace.ringCatSheaf i.ker.support)
      (c : ℤ) ⋙
    SheafOfModules.ClosedSubset.pushforward X.toRingedSpace.ringCatSheaf i.ker.support

end AlgebraicGeometry.Scheme.Hom.LocalCohomology

end
