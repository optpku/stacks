/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion
public import ReasLib.Algebra.Module.Torsion.SupportColimit

@[expose] public section

open CategoryTheory DerivedCategory

noncomputable section

universe u

namespace CategoryTheory
namespace DerivedCategory
namespace LocalCohomology
namespace Completion

variable {A : Type u} [CommRing A]

/-- If `A` is `I`-adically complete, degree-zero cohomology of the derived `I`-adic
completion of local cohomology supported on `PrimeSpectrum.zeroLocus J` is the support
colimit of the admissible primary components of `M`. -/
theorem cohomologyZeroSupportColimit [IsNoetherianRing A] (I J : Ideal A)
    [IsAdicComplete I A] (M : ModuleCat.{u} A) [Module.Finite A M]
    (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (hRΓZ : IdealPowerTorsion.inclusion J ⊣ RΓZ) :
    IsIsomorphic
      ((homologyFunctor (ModuleCat.{u} A) 0).obj
        (derivedCompletionOf I I.fg_of_isNoetherianRing
          (RΓZ.obj (ModuleCat.single0 M)).obj))
      (ModuleCat.of A (Ideal.supportColimit I J M)) := sorry

end Completion
end LocalCohomology
end DerivedCategory
end CategoryTheory
