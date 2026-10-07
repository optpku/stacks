module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport

/-!
# Coherent modules on scheme-theoretic supports

This leaf upgrades finite-type descent to a scheme-theoretic support to coherent descent on
locally Noetherian schemes.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsSchemeTheoreticSupport

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A coherent module on a locally Noetherian scheme descends to a coherent module on any
ideal-sheaf datum realizing its scheme-theoretic support. -/
theorem exists_coherent_module
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (I : X.IdealSheafData) (hI : IsSchemeTheoreticSupport ℱ I) :
    ∃ 𝒢 : I.subscheme.Modules,
      ∃ _ : 𝒢.IsCoherent,
        Nonempty ((pushforward I.subschemeι).obj 𝒢 ≅ ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.IsSchemeTheoreticSupport
