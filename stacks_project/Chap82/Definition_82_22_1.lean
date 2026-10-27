/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.RelativeCartier
import StacksCheckRecall

/-!
# Definition 82.22.1

The refined Gysin homomorphism associated to a global section of an invertible
module on a good algebraic space, and Cartier intersection when the zero scheme
is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Definition 82.22.1 (1): In Situation 82.2.1, for good `X / B`, an invertible
sheaf `L` and a global section `s`, with `D = Z(s)` and `i : D ⟶ X` the closed
immersion, the refined Gysin homomorphism
`i* : Z_{k+1}(X) ⟶ CH_k(D)` is `Hom.gysin f δ k L s`. On an integral closed
subspace `W ⊂ X` of `δ`-dimension `k + 1` it is `[D ∩ W]_k` if `W ⊄ D`, and
`i'_*(c1(L|_W) ∩ [W])` if `W ⊂ D`, extended linearly to general
`(k + 1)`-cycles. -/
@[stacks 0ER1] #check (AlgebraicGeometry.AlgebraicSpace.Hom.gysin :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (L : X.Modules) [isInvertibleObject L] (s : L.sections),
      Hom.cycleGroup f δ (k + 1) →+ Hom.chowGroup (zeroSchemeι L s ≫ f) δ k)

/- Definition 82.22.1 (2): If `D` is an effective Cartier divisor, then
`D · α = i_* i* α` is `Hom.cartierIntersection f δ k L s`, the pushforward of
the Gysin class to a class on `X`. -/
@[stacks 0ER1] #check (AlgebraicGeometry.AlgebraicSpace.Hom.cartierIntersection :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (L : X.Modules) [isInvertibleObject L] (s : L.sections)
      [IsEffectiveCartierDivisor (zeroSchemeι L s)],
      Hom.cycleGroup f δ (k + 1) →+ Hom.chowGroup f δ k)
