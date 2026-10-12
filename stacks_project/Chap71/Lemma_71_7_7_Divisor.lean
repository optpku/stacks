/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme

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
theorem zeroScheme_isLocallyPrincipalClosedSubspace {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    IsLocallyPrincipalClosedSubspace (zeroSchemeι L s) :=
  sorry

/-- The closed immersion of a zero scheme is locally principal. -/
instance instIsLocallyPrincipalClosedSubspace_zeroSchemeι {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] (s : L.sections) :
    IsLocallyPrincipalClosedSubspace (zeroSchemeι L s) :=
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
  sorry

end AlgebraicGeometry.AlgebraicSpace
