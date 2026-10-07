module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Sequential
public import ReasLib.Algebra.Module.IdealPower.Submodule.Sequential
public import ReasLib.CategoryTheory.Pro.Representative

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn
open scoped ZeroObject

noncomputable section

universe u

namespace Ideal.LocalCohomology.AlgebraizationSituation

/-- The supported local-cohomology tower of exact adic stages has pro-value zero through degree `s`. -/
theorem proZero_adicCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : AlgebraizationSituation H I M T s d) :
    ∀ i : ℤ, i ≤ s →
      CategoryTheory.Pro.HasValue
        (supportedCohomologyTower T
          (Ideal.PowerSubmodule.system I (ModuleCat.of A M)) i)
        (0 : ModuleCat.{u} A) := sorry

/-- Degree-`s + 1` transition images in the supported local-cohomology tower eventually inject into one fixed stage. -/
theorem exists_eventually_mono_adicCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : AlgebraizationSituation H I M T s d) :
    ∃ (m₀ : ℕ), ∀ (m : ℕ) (h_m₀m : m₀ ≤ m),
      ∃ (m' : ℕ) (h_mm' : m ≤ m'), ∀ (k : ℕ) (h_m'k : m' ≤ k),
        Mono
          ((imageSubobject
              ((supportedCohomologyTower T
                (Ideal.PowerSubmodule.system I (ModuleCat.of A M)) (s + 1)).transitionMap
                (Nat.le_trans h_mm' h_m'k))).arrow ≫
            (supportedCohomologyTower T
              (Ideal.PowerSubmodule.system I (ModuleCat.of A M)) (s + 1)).transitionMap
              h_m₀m) := sorry

end Ideal.LocalCohomology.AlgebraizationSituation

end
