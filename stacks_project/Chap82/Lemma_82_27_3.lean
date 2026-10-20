/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Lemma_82_27_3_AssociatedVectorBundle
public import stacks_project.Chap82.Lemma_82_25_1_ChowPullback

/-!
# Flat pullback along the associated vector bundle is a Chow isomorphism

In the good setup of Situation 82.2.1, flat pullback along the projection of
the associated vector bundle of a finite locally free module of rank `r` is
bijective on Chow groups.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 82.27.3: In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free sheaf of rank `r` on `X`. Let
`p : associatedVectorBundleOfRank E r ⟶ X` be the associated vector bundle over
`X`. Then `chowFlatPullback : CH_k(X) → CH_{k+r}(associatedVectorBundleOfRank E r)`
is an isomorphism for all `k : ℤ`. -/
@[stacks 0ERW]
theorem chowFlatPullback_bijective_associatedVectorBundleOfRank {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) :
    Function.Bijective
      (chowFlatPullback pX (associatedVectorBundleOfRankπ E r ≫ pX) δ
        (associatedVectorBundleOfRankπ E r) r rfl k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
