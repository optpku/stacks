module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {J : X.IdealSheafData}

/-- The inverse system whose stage `n` is the degree-`p` cohomology over `A` of the
`n`th stage of a coherent formal module on `X`. -/
noncomputable abbrev cohomologySystem
    (F : X.CoherentFormalModules J) (f : X ⟶ Spec (CommRingCat.of A)) (p : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  F.obj ⋙ (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
    DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ) ⋙
    RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace ⋙
    ModuleCat.derivedRestrictionOfScalars f.appTop.hom ⋙
    ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⋙
    DerivedCategory.homologyFunctor (ModuleCat A) p

/-- Stage `n` of `cohomologySystem F f p` is the degree-`p` homology of the derived
global sections of the `n`th coherent module in `F`, with scalars restricted to `A`. -/
theorem cohomologySystem_obj
    (F : X.CoherentFormalModules J) (f : X ⟶ Spec (CommRingCat.of A)) (p : ℤ) (n : ℕ) :
    (cohomologySystem F f p).obj (op n) =
      (DerivedCategory.homologyFunctor (ModuleCat A) p).obj
        ((ModuleCat.derivedRestrictionOfScalars
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).obj
          ((ModuleCat.derivedRestrictionOfScalars f.appTop.hom).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
              ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
                ((SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι.obj
                  (F.obj.obj (op n))))))) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
