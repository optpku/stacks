module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.EulerCharacteristic.Pushforward

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 72.17.3
The Euler characteristic of a coherent module on an algebraic space proper over a
field is the alternating sum of the Euler characteristics of its higher direct images.
-/
@[stacks 0EDD] #check
  (AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic_eq_finsum_higherDirectImage_of_proper_over_field :
    ∀ {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    (𝒢 : Y.Modules) [𝒢.IsCoherent],
    eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase Y) 𝒢 =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) *
          eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X)
            (Modules.higherDirectImage f 𝒢 i))
