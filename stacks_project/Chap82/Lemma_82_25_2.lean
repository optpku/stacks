/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Lemma_82_25_2_AssociatedVectorBundle
public import stacks_project.Chap82.Lemma_82_25_1_ChowPullback

/-!
# Flat pullback along the associated line bundle is a Chow isomorphism

In the good setup of Situation 82.2.1, flat pullback along the projection of
the associated vector bundle of an invertible module is bijective on Chow
groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 82.25.2: In Situation 82.2.1 let `X / B` be good. Let `L` be an
invertible `𝒪_X`-module. Let `p : associatedVectorBundle L ⟶ X` be the
associated vector bundle over `X`. Then
`chowFlatPullback : CH_k(X) → CH_{k+1}(associatedVectorBundle L)` is an
isomorphism for all `k : ℤ`. -/
@[stacks 0ERH]
theorem chowFlatPullback_bijective_associatedVectorBundle {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (k : ℤ) :
    Function.Bijective
      (chowFlatPullback pX (associatedVectorBundleπ L ≫ pX) δ
        (associatedVectorBundleπ L) 1 rfl k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
