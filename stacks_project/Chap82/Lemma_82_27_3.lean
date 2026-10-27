/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback.VectorBundle

/-!
# Flat pullback along the associated vector bundle is a Chow isomorphism

In the good setup of Situation 82.2.1, flat pullback along the projection of
the associated vector bundle of a finite locally free module of rank `r` is
bijective on Chow groups.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 82.27.3: In Situation 82.2.1 let `X / B` be good. Flat pullback
along the associated vector bundle `Spec(Sym E) → X` of a finite locally free
module of rank `r` is an isomorphism from `CH_k(X)` to `CH_{k+r}(Spec(Sym E))`
for every integer `k`. -/
@[stacks 0ERW]
#check (AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback_linearSpace_bijective :
  ∀ {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ),
    Function.Bijective
      (AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback pX
        (Modules.linearSpaceπ E ≫ pX) δ (Modules.linearSpaceπ E) r rfl k))

