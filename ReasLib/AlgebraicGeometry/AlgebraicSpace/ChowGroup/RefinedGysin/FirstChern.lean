/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-!
# Refined Gysin pushforward and first Chern classes

Pushing refined intersection with the zero scheme of an invertible-module
section into the ambient algebraic space gives cap product with its first
Chern class. For an effective Cartier zero divisor, this identifies Cartier
intersection with first Chern cap product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable (k : ℤ)

/-- Pushing the refined Gysin class of a cycle along the zero-scheme immersion
equals capping that cycle with the first Chern class of the defining invertible
module. -/
theorem chowPushforward_gysin_eq_firstChernClassCap
    (α : cycleGroup f δ (k + 1)) :
    chowPushforward f δ (zeroScheme L s) k (gysin f δ k L s α) =
      firstChernClassCap f δ L k α :=
  sorry

/-- Intersection with an effective Cartier zero divisor equals cap product
with the first Chern class of its defining invertible module. -/
theorem cartierIntersection_eq_firstChernClassCap
    [IsEffectiveCartierDivisor (zeroSchemeι L s)]
    (α : cycleGroup f δ (k + 1)) :
    cartierIntersection f δ k L s α = firstChernClassCap f δ L k α := by
  simpa only [cartierIntersection_eq] using
    chowPushforward_gysin_eq_firstChernClassCap f δ L s k α

end AlgebraicGeometry.AlgebraicSpace.Hom
