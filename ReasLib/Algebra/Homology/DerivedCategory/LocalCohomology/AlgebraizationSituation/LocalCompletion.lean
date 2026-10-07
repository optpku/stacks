module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion.Comparison
public import ReasLib.Algebra.Module.IdealPower.Predicate

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology
open CategoryTheory.DerivedCategory.LocalCohomology.Completion

noncomputable section

universe u

namespace Ideal.LocalCohomology.AlgebraizationSituation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- Under the algebraization hypotheses, local cohomology in bounded degrees is
identified by the canonical map with the limit of the quotient tower. -/
theorem cohomologyToLimit_bijective
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (s d : ℤ)
    (h : AlgebraizationSituation H I (M : Type u)
      ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) s d)
    (RΓm : DerivedCategory (ModuleCat.{u} A) ⥤
      IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓm : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓm) :
    ∀ i : ℤ, i ≤ s →
      Function.Bijective
        (Completion.cohomologyToLimit I (IsLocalRing.maximalIdeal A) RΓm M i) := sorry

/-- Under the same hypotheses, both local-cohomology endpoints in every
bounded degree are annihilated by a power of the ideal. -/
theorem cohomology_annihilatedByPower
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (s d : ℤ)
    (h : AlgebraizationSituation H I (M : Type u)
      ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) s d)
    (RΓm : DerivedCategory (ModuleCat.{u} A) ⥤
      IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓm : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓm) :
    ∀ i : ℤ, i ≤ s →
      Module.IsAnnihilatedByPower I
        ((homologyFunctor (ModuleCat.{u} A) i).obj
          (RΓm.obj (ModuleCat.single0 M)).obj) ∧
      Module.IsAnnihilatedByPower I
        ((limit
          (quotientSystem I (IsLocalRing.maximalIdeal A) RΓm M ⋙
            homologyFunctor (ModuleCat.{u} A) i)) : ModuleCat.{u} A) := sorry

end Ideal.LocalCohomology.AlgebraizationSituation
