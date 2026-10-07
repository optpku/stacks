module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap82.Lemma_82_25_1_AffineFiber
public import stacks_project.Chap82.Lemma_82_25_1_CyclePullback
public import stacks_project.Chap82.Lemma_82_25_1_ChowPullback

/-!
# Surjectivity of flat pullback on Chow groups of affine-space fibres

In the good setup of Situation 82.2.1, a quasi-compact flat morphism of
relative dimension `r` whose fibres are affine `r`-space induces a surjective
map on Chow groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 82.25.1: In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a quasi-compact flat morphism over `B` of relative dimension
`r`. Assume that for every `y : Points Y` we have
`X_y ≅ AffineSpace (ULift (Fin r))` over `κ(y)`. Then
`chowFlatPullback : CH_k(Y) → CH_{k+r}(X)` is surjective for all `k : ℤ`. -/
@[stacks 0ERG]
theorem chowFlatPullback_surjective {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [QuasiCompact f] [Flat f] [RelativeDimension f r]
    [IsDecent Y] (hf : f ≫ pY = pX)
    (h_fiber : ∀ y : Points Y, IsAffineSpaceFiber f r y) (k : ℤ) :
    Function.Surjective (chowFlatPullback pY pX δ f r hf k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
