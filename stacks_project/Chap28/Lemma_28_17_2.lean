module

import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization.QuasiCompact
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.17.2 (1): for a quasi-compact scheme, the canonical localized twisted-section
comparison is injective. -/
@[stacks 01PW] #check
  (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison_injective :
    ∀ {X : Scheme.{u}} [CompactSpace X]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤)),
      Function.Injective
        (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison L F s))

/- Lemma 28.17.2 (2): for a quasi-compact and quasi-separated scheme, the canonical localized
twisted-section comparison is bijective. -/
@[stacks 01PW] #check
  (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison_bijective :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤)),
      Function.Bijective
        (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison L F s))

/- Lemma 28.17.2 (3): for the tensor-unit module on a quasi-compact and quasi-separated scheme,
the canonical localized twisted-section comparison is bijective. -/
@[stacks 01PW] #check
  (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison_unit_bijective :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L] (s : Γ(L, ⊤)),
      Function.Bijective
        (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison
          L (𝟙_ X.Modules) s))

/- A standard fraction is evaluated by restriction and contraction with the canonical
nonvanishing trivialization. -/
#check
  (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison_apply_mk :
    ∀ {X : Scheme.{u}} (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (F : X.Modules) (s : Γ(L, ⊤)) (n : ℕ)
      (m : AlgebraicGeometry.RingedSpace.GradedSections.twistedDegree L F (n : ℤ)),
      AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison L F s
          (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedMk L F s n m) =
        AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedFractionValue L F s n m)
