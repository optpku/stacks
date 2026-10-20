module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier

/-!
# Divisor properties of zero schemes on algebraic spaces

The zero scheme of a section of an invertible module is locally principal, and
it is an effective Cartier divisor if and only if the section is regular.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The zero scheme of a section of an invertible module is a locally principal
closed subspace. -/
@[instance]
theorem zeroScheme_isLocallyPrincipalClosedSubspace {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    IsLocallyPrincipal (zeroSchemeι L s) :=
  sorry

/-- The zero scheme of a section of an invertible module is an effective Cartier
divisor if and only if the section is regular. -/
theorem zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    IsEffectiveCartierDivisor (zeroSchemeι L s) ↔ IsRegularSection L s :=
  sorry

/-- A regular section of an invertible module cuts out an effective Cartier
divisor. -/
instance instIsEffectiveCartierDivisor_zeroSchemeι {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    [IsRegularSection L s] : IsEffectiveCartierDivisor (zeroSchemeι L s) :=
  (zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection L s).mpr inferInstance

end AlgebraicGeometry.AlgebraicSpace
