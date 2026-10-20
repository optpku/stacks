module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FlatPullbackSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- For a coherent module `F` on the punctured spectrum of a Noetherian local ring `A`,
cohomology of the derived `I`-adic completion of `RΓ(U, F)` is isomorphic to the inverse
limit of the cohomology of the quotient sheaves `F / I ^ (n + 1) F`. -/
@[stacks 0DXI]
theorem completionCohomologyIsIsomorphicLimit
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : RingedSpace.Coh (scheme A).toRingedSpace) (I : Ideal A) (i : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (DerivedCategory.derivedCompletionOf I I.fg_of_isNoetherianRing
          ((Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι).obj
            ((DerivedCategory.singleFunctor
              (scheme A).toRingedSpace.Modules (0 : ℤ)).obj F.obj))))
      (limit
        (CategoryTheory.SequentialInverseSystem.shift
            (PowerQuotientModule.system.{u, u, u}
              (((Scheme.idealSheafDataOfIdealOnSpec I).comap
                (puncturedOpen A).ι).toSubobject) F.obj) 1 ⋙
          DerivedCategory.singleFunctor
            (scheme A).toRingedSpace.Modules (0 : ℤ) ⋙
          Scheme.FlatPullbackSections.baseSections (puncturedOpen A).ι ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
