/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.FirstChern
import StacksCheckRecall

/-!
# Gysin pushforward versus first Chern class

On a good algebraic space, pushing the refined Gysin class of a cycle along the
zero-scheme immersion recovers intersection with the first Chern class of the
defining invertible module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Lemma 82.22.4 (1): In Situation 82.2.1 let `X / B` be good. Let
`(L, s, i : D ⟶ X)` be as in Definition 82.22.1. Let `α` be a `(k + 1)`-cycle
on `X`. Then `i_* i^* α = c1(L) ∩ α` in `CH_k(X)`. -/
@[stacks 0ER4] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.chowPushforward_gysin_eq_firstChernClassCap :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L] (s : L.sections)
      (k : ℤ) (α : Hom.cycleGroup f δ (k + 1)),
      Hom.chowPushforward f δ (zeroScheme L s) k (Hom.gysin f δ k L s α) =
        Hom.firstChernClassCap f δ L k α)

/- Lemma 82.22.4 (2): If `D` is an effective Cartier divisor, then
`D · α = c1(O_X(D)) ∩ α`. The effective Cartier pair `(L, s)` represents
`O_X(D)`, as explained in the source section introduction. -/
@[stacks 0ER4] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.cartierIntersection_eq_firstChernClassCap :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L] (s : L.sections)
      (k : ℤ) [IsEffectiveCartierDivisor (zeroSchemeι L s)]
      (α : Hom.cycleGroup f δ (k + 1)),
      Hom.cartierIntersection f δ k L s α = Hom.firstChernClassCap f δ L k α)
