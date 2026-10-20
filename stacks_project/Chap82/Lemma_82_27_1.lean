/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectivePushforward

/-!
# Projective bundle Chern-power pushforward

For a finite locally free module of rank `r = q + 1`, pushforward of
`c₁(𝒪_P(1))^s ∩ π^* α` vanishes below degree `q` and equals `α` in degree `q`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

universe u

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/- Lemma 82.27.1 (1): Chern powers below the projective fibre dimension have
zero pushforward for every Chow class. -/
@[stacks 0ERU] #check (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern.pushforwardC1PowerCap_eq_zero_of_lt f δ E q :
  ∀ (k : ℤ) (s : ℕ), s < q → ∀ α : Hom.chowGroup f δ k,
    HigherChern.pushforwardC1PowerCap f δ E q k s α = 0)

/- Lemma 82.27.1 (2): The top tautological Chern power has identity pushforward,
expressed by the zero-index Segre map with canonical degree transport. -/
@[stacks 0ERU] #check (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern.segre_zero f δ E q :
  ∀ k : ℤ, HigherChern.segre f δ E q 0 k =
      ChowCohomology.castChowGroup δ f (show k = k - (0 : ℕ) by omega))
