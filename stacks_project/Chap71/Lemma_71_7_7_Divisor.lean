module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.ZeroScheme

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

#check (AlgebraicGeometry.AlgebraicSpace.zeroScheme_isLocallyPrincipalClosedSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections),
    IsLocallyPrincipal (zeroSchemeι L s))

#check (AlgebraicGeometry.AlgebraicSpace.zeroScheme_isEffectiveCartierDivisor_iff_isRegularSection :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections),
    IsEffectiveCartierDivisor (zeroSchemeι L s) ↔ IsRegularSection L s)

#check (AlgebraicGeometry.AlgebraicSpace.instIsEffectiveCartierDivisor_zeroSchemeι :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] (s : L.sections) [IsRegularSection L s],
    IsEffectiveCartierDivisor (zeroSchemeι L s))
