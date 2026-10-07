module

public import stacks_project.Chap72.Lemma_72_17_3_EulerCharacteristic
public import stacks_project.Chap72.Lemma_72_17_3_Instances

/-!
# Lemma 72.17.3

The Euler characteristic of a coherent module on an algebraic space proper over a
field is the alternating sum of the Euler characteristics of its higher direct
images along a morphism to another algebraic space proper over that field.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 72.17.3: let `k` be a field, let `f : Y ⟶ X` be a morphism of algebraic
spaces proper over `k`, and let `𝒢` be a coherent `𝒪_Y`-module. Then
`χ(Y, 𝒢)` equals the alternating sum of `χ(X, R^i f_* 𝒢)`. -/
@[stacks 0EDD]
theorem eulerCharacteristic_eq_finsum_higherDirectImage_of_proper_over_field
    {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (toBase X)] [Proper (toBase Y)]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    (𝒢 : Y.Modules) [𝒢.IsCoherent] :
    eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (toBase Y) 𝒢 =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) *
          eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (toBase X)
            (Modules.higherDirectImage f 𝒢 i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
