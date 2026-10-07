module

import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Cohomology.Affine
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.GradedSections
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

/- Lemma 30.17.4: let `X` be a quasi-compact and quasi-separated scheme, let `L` be an
invertible `𝒪_X`-module, and let `s ∈ Γ(X, L)` have affine nonvanishing open. For
every quasicoherent `𝒪_X`-module `F`, every `p > 0`, and every `ξ ∈ H^p(X, F)`,
some nonnegative power of `s` annihilates `ξ` in `H^p(X, F ⊗ L^n)`. -/
@[stacks 01XR] #check
  (AlgebraicGeometry.Scheme.Modules.GradedSections.exists_twistedCohomologyPowSmul_eq_zero_of_isAffineOpen :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (L : X.Modules) [hL : AlgebraicGeometry.Scheme.Modules.Invertible L]
      (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤))
      (hAffine : IsAffineOpen (hL.sectionNonvanishingOpen s))
      (p : ℕ) (hp : 0 < p)
      (ξ : RingedSite.Hom.moduleGlobalCohomology
        (X := RingedSpace.opensRingedSite X.toRingedSpace) F p),
      ∃ n : ℕ,
        DirectSum.component ℤ ℤ (twistedCohomologyDegree L F p) (n : ℤ)
            ((degreeOne L s : RingedSpace.GradedSections.ring L) ^ n •
              DirectSum.of (twistedCohomologyDegree L F p) (0 : ℤ)
                ((RingedSite.Hom.moduleGlobalCohomologyMap
                  (X := RingedSpace.opensRingedSite X.toRingedSpace)
                  ((ρ_ F).inv ≫
                    (Iso.refl F ⊗ᵢ RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
                    (Iso.refl F ⊗ᵢ RingedSpace.InvertiblePower.zeroIso L).inv) p).hom ξ)) = 0)
