/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_18_1_ChernCap
public import stacks_project.Chap82.Definition_82_22_1_Gysin

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

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable (k : ℤ)

/-- Lemma 82.22.4 (1): In Situation 82.2.1 let `X / B` be good. Let
`(L, s, i : D ⟶ X)` be as in Definition 82.22.1. Let `α` be a `(k + 1)`-cycle
on `X`. Then `i_* i^* α = c1(L) ∩ α` in `CH_k(X)`. -/
@[stacks 0ER4]
theorem chowPushforward_gysin_eq_firstChernClassCap
    (α : cycleGroup f δ (k + 1)) :
    chowPushforward f δ (zeroScheme L s) k (gysin f δ k L s α) =
      firstChernClassCap f δ L k α :=
  sorry

/-- Lemma 82.22.4 (2): In particular, if `D` is an effective Cartier divisor,
then `D · α = c1(O_X(D)) ∩ α`, identifying `O_X(D)` with `L` by Lemma 71.7.8. -/
@[stacks 0ER4]
theorem cartierIntersection_eq_firstChernClassCap
    [IsEffectiveCartierDivisor (zeroSchemeι L s)]
    (α : cycleGroup f δ (k + 1)) :
    cartierIntersection f δ k L s α = firstChernClassCap f δ L k α :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
