/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.TwistedHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization.QuasiCompact

/-!
# Localized graded morphisms on quasi-compact schemes
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.TwistedHom

variable {X : Scheme.{u}}

/-- On a quasi-compact scheme, the canonical comparison from localized twisted morphisms to
morphisms between the restrictions on the nonvanishing open is injective when the source module
is of finite type. -/
theorem localizedComparison_injective
    [CompactSpace X]
    (L : X.Modules) [Invertible L]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsFiniteType]
    (s : Γ(L, ⊤)) :
    Function.Injective (localizedComparison L F G s) := sorry

/-- On a quasi-compact and quasi-separated scheme, the canonical comparison from localized
twisted morphisms to morphisms between the restrictions on the nonvanishing open is bijective
when the source module is of finite presentation. -/
theorem localizedComparison_bijective
    [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [Invertible L]
    (F G : X.Modules) [G.IsQuasicoherent] [F.IsFinitePresentation]
    (s : Γ(L, ⊤)) :
    Function.Bijective (localizedComparison L F G s) := sorry

end AlgebraicGeometry.Scheme.Modules.TwistedHom
