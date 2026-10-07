module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory

noncomputable section

universe u

namespace CategoryTheory
namespace DerivedCategory
namespace LocalCohomology
namespace Completion

/- Lemma 52.5.4: the cohomology in degree `i` of the derived `I`-adic completion
of maximal-ideal local cohomology of `M` is isomorphic to the inverse limit of
the corresponding cohomology objects for the positive system of quotients of `M`. -/
@[stacks 0DXJ] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.Completion.cohomologyIsIsomorphicLimit :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
      (RΓm : DerivedCategory (ModuleCat.{u} A) ⥤
        IdealPowerTorsion (IsLocalRing.maximalIdeal A))
      (hRΓm : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓm)
      (i : ℤ),
      IsIsomorphic
        ((homologyFunctor (ModuleCat.{u} A) i).obj
          (derivedCompletionOf I I.fg_of_isNoetherianRing
            (RΓm.obj (ModuleCat.single0 M)).obj))
        (limit (quotientSystem I (IsLocalRing.maximalIdeal A) RΓm M ⋙
          homologyFunctor (ModuleCat.{u} A) i)))

end Completion
end LocalCohomology
end DerivedCategory
end CategoryTheory
