module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport

/-!
# Support of a module and its zeroth Fitting ideal sheaf

This module compares the closed subscheme defined by the zeroth Fitting ideal
sheaf with scheme-theoretic and point-set support, and records descent to that
closed subscheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The zeroth Fitting ideal sheaf is contained in every ideal-sheaf datum that
has the affine annihilator characterization of scheme-theoretic support. -/
theorem fittingIdealSheaf_zero_le_schemeTheoreticSupport
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (I : S.IdealSheafData) (hI : IsSchemeTheoreticSupport F I) :
    Scheme.fittingIdealSheaf F 0 ≤ I := sorry

/-- The closed subset cut out by the zeroth Fitting ideal sheaf is the ordinary
point-set support of a finite-type quasicoherent module. -/
theorem fittingIdealSheaf_zero_support_eq_moduleSupport
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ((Scheme.fittingIdealSheaf F 0).support : Set S) =
      RingedSpace.moduleSupport F := sorry

/-- A finite-type quasicoherent module is the pushforward of a finite-type
quasicoherent module on the closed subscheme defined by its zeroth Fitting
ideal sheaf. -/
theorem exists_finiteType_module_pushforward_fittingIdealSheaf_zero
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ G0 : (Scheme.fittingIdealSheaf F 0).subscheme.Modules,
      ∃ _ : G0.IsQuasicoherent,
        ∃ _ : G0.IsFiniteType,
          Nonempty ((pushforward (Scheme.fittingIdealSheaf F 0).subschemeι).obj G0 ≅
            F) := sorry

end AlgebraicGeometry.Scheme.Modules
