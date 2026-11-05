module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Effective Cartier divisors

This leaf owns effective Cartier divisors as closed immersions with invertible
ideal sheaf, together with the ideal-sheaf-data presentation used by divisor
and blowup arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A scheme morphism defines an effective Cartier divisor when it is a closed immersion whose
ideal sheaf is invertible for the canonical tensor product on ambient scheme modules. -/
class IsEffectiveCartierDivisor {S D : Scheme.{u}} (i : D ⟶ S) : Prop
    extends IsClosedImmersion i where
  /-- The closed-immersion ideal sheaf is tensor-invertible. -/
  invertibleIdealSheaf :
    Scheme.Modules.Invertible (RingedSpace.Hom.idealSheaf i.toShHom)

attribute [instance] IsEffectiveCartierDivisor.invertibleIdealSheaf

/-- Unfold the effective-Cartier condition into closedness and invertibility of the ideal sheaf. -/
theorem isEffectiveCartierDivisor_iff {S D : Scheme.{u}} (i : D ⟶ S) :
    IsEffectiveCartierDivisor i ↔
      IsClosedImmersion i ∧
        Scheme.Modules.Invertible
          (RingedSpace.Hom.idealSheaf i.toShHom) := sorry

/-- Every effective Cartier divisor is a locally principal closed subscheme. -/
instance isLocallyPrincipalClosedSubscheme_of_isEffectiveCartierDivisor
    {S D : Scheme.{u}} {i : D ⟶ S}
    [IsEffectiveCartierDivisor i] :
    IsLocallyPrincipalClosedSubscheme i := sorry

end AlgebraicGeometry
