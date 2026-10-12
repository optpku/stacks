/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.TwistedHom
import stacks_project.Chap28.«28_17_1_1»
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable (L : X.Modules) [Invertible L]
variable (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
variable (s : Γ(L, ⊤))

/- 28.17.2.1: The localization of
`⨁ n : ℤ, (F ⟶ G ⊗ (L ^⊗ n))` at the degree-one section `s` maps canonically to the
morphisms from `F` to `G` on the nonvanishing open of `s`. -/
@[stacks 0B5M]
#check (AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedComparison L F G s :
  AlgebraicGeometry.Scheme.Modules.TwistedHom.localized L F G s →+
    (F.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
        (RingedSpace.sectionFromTop L s)) ⟶
      G.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
        (RingedSpace.sectionFromTop L s))))

#check (AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedComparison_apply_mk L F G s :
  ∀ (n : ℕ)
      (α : AlgebraicGeometry.Scheme.Modules.TwistedHom.degree L F G (n : ℤ)),
    AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedComparison L F G s
        (AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedMk L F G s n α) =
      α.over (RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
          (RingedSpace.sectionFromTop L s)) ≫
        AlgebraicGeometry.Scheme.Modules.Invertible.nonvanishingTwistContraction L G s n)

end AlgebraicGeometry.Scheme.Modules
