/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.GysinFirstChern
import StacksCheckRecall

/-!
# Gysin of a zero scheme commutes with first-Chern cap

In Situation 82.2.1, on a good algebraic space, the Chow-level Gysin map of a
Definition 82.22.1 triple commutes with intersecting by the first Chern class
of an invertible module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.23.3: In Situation 82.2.1 let `X / B` be good. Let
`(L, s, i : D ⟶ X)` be a triple as in Definition 82.22.1, with `D` the zero
scheme of `s` and `i = zeroSchemeι L s`. Let `N` be an invertible `X.Modules`
object. Then `i*(c1(N) ∩ α) = c1(i* N) ∩ i* α` in
`chowGroup (zeroSchemeι L s ≫ f) δ k` for all
`α : chowGroup f δ (k + 1 + 1)`, where `i*` is `ChowGroup.RefinedGysin.gysin f δ L s`
and `c1(-) ∩ -` is `FirstChernChow.cap`. The source degrees `CH_k(X)` and `CH_{k-2}(D)` are
reindexed so both maps land in degree `k`; the printed source `CH_k(Z)` is
`CH_k(X)`. -/
@[stacks 0ERB]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.chowGysin_firstChernCap :
    ∀ {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    (N : X.Modules) [isInvertibleObject N]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj N)]
    (k : ℤ) (α : chowGroup f δ (k + 1 + 1)),
    ChowGroup.RefinedGysin.gysin f δ L s k (FirstChernChow.cap f δ N (k + 1) α) =
      FirstChernChow.cap (zeroSchemeι L s ≫ f) δ
        ((Modules.pullback (zeroSchemeι L s)).obj N) k
        (ChowGroup.RefinedGysin.gysin f δ L s (k + 1) α))

end AlgebraicGeometry.AlgebraicSpace.Hom
