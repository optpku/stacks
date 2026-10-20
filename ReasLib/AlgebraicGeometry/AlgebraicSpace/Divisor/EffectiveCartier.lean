/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyPrincipal

/-!
# Effective Cartier divisors on algebraic spaces

A closed immersion of algebraic spaces is an effective Cartier divisor when its
associated ideal sheaf is an invertible module on the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is an effective Cartier divisor when it is a closed
immersion whose associated ideal sheaf is an invertible `𝒪_X`-module. -/
class IsEffectiveCartierDivisor {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) : Prop extends IsClosedImmersion i where
  /-- The associated ideal sheaf is tensor-invertible. -/
  invertibleIdealSheaf : isInvertibleObject (Hom.idealSheaf i)

/-- Effective Cartier unfolds as a closed immersion whose ideal sheaf is invertible. -/
theorem isEffectiveCartierDivisor_iff {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) :
    IsEffectiveCartierDivisor i ↔
      IsClosedImmersion i ∧ isInvertibleObject (Hom.idealSheaf i) :=
  sorry

attribute [instance] IsEffectiveCartierDivisor.invertibleIdealSheaf

/-- Every effective Cartier divisor is a locally principal closed subspace. -/
instance IsEffectiveCartierDivisor.isLocallyPrincipal
    {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] : IsLocallyPrincipal i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
