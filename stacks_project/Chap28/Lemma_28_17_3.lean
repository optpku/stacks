/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.TwistedHom.QuasiCompact
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 28.17.3 (1): If `X` is quasi-compact and `F` is of finite type, then the canonical
comparison from localized twisted morphisms to morphisms on the nonvanishing open is injective. -/
@[stacks 01XQ]
#check (AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedComparison_injective :
  ∀ {X : Scheme.{u}} [CompactSpace X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsFiniteType]
    (s : Γ(L, ⊤)),
    Function.Injective
      (AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedComparison L F G s))

/- Lemma 28.17.3 (2): If `X` is quasi-compact and quasi-separated and `F` is of finite
presentation, then the canonical comparison from localized twisted morphisms to morphisms on the
nonvanishing open is bijective. -/
@[stacks 01XQ]
#check (AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedComparison_bijective :
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (F G : X.Modules) [G.IsQuasicoherent] [F.IsFinitePresentation]
    (s : Γ(L, ⊤)),
    Function.Bijective
      (AlgebraicGeometry.Scheme.Modules.TwistedHom.localizedComparison L F G s))
