module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.DerivedCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 52.11.1: for a coherent module `F` on the punctured spectrum of a
Noetherian local ring `A`, cohomology of the derived `I`-adic completion of
`RΓ(U, F)` is the inverse limit of the cohomology of `F / I ^ (n + 1) F`. -/
@[stacks 0DXI]
#check (AlgebraicGeometry.PuncturedSpectrum.completionCohomologyIsIsomorphicLimit :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (F : RingedSpace.Coh (scheme A).toRingedSpace) (I : Ideal A) (i : ℤ),
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
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)))

end AlgebraicGeometry.PuncturedSpectrum
