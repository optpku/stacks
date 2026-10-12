/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GlobalSections.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization

/-!
# Localized twisted sections on quasi-compact schemes
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GradedSections

variable {X : Scheme.{u}}

/-- On a quasi-compact scheme, the canonical comparison from localized twisted global sections
to sections on the nonvanishing open is injective. -/
theorem localizedTwistedComparison_injective
    [CompactSpace X] (L : X.Modules) [Invertible L]
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤)) :
    Function.Injective (localizedTwistedComparison L F s) := sorry

/-- On a quasi-compact and quasi-separated scheme, the canonical comparison from localized
twisted global sections to sections on the nonvanishing open is bijective. -/
theorem localizedTwistedComparison_bijective
    [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [Invertible L]
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤)) :
    Function.Bijective (localizedTwistedComparison L F s) := sorry

/-- For the tensor-unit module on a quasi-compact and quasi-separated scheme, the canonical
comparison from localized twisted global sections to sections on the nonvanishing open is
bijective. -/
theorem localizedTwistedComparison_unit_bijective
    [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [Invertible L] (s : Γ(L, ⊤)) :
    Function.Bijective (localizedTwistedComparison L (𝟙_ X.Modules) s) := sorry

end AlgebraicGeometry.Scheme.Modules.GradedSections
