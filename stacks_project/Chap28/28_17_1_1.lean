module

import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization
import stacks_project.Chap28.Lemma_28_17_1
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- 28.17.1.1: for a scheme `X`, an invertible `𝒪_X`-module `L`, an `𝒪_X`-module `F`,
and `s : Γ(L, ⊤)`, the canonical map sends the degree-zero homogeneous localization
`Γ_*(X, L, F)_(s)` to `Γ(F, X_s)` on the nonvanishing open of `s`. -/
@[stacks 0B5L]
#check (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedComparison :
  ∀ {X : Scheme.{u}} (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (F : X.Modules) (s : Γ(L, ⊤)),
    AlgebraicGeometry.Scheme.Modules.localizedTwistedGlobalSections L F s →+
      AlgebraicGeometry.Scheme.Modules.nonvanishingOpenSections L F s)
