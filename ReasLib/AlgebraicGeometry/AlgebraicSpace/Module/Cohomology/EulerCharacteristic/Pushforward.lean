module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.RelativeEulerCharacteristic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.ProperOverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Euler characteristics of higher direct images

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

/-- Let `k` be a field, let `f : Y ⟶ X` be a morphism of algebraic
spaces proper over `k`, and let `𝒢` be a coherent `𝒪_Y`-module. Then
`χ(Y, 𝒢)` equals the alternating sum of `χ(X, R^i f_* 𝒢)`. -/
@[stacks 0EDD]
theorem eulerCharacteristic_eq_finsum_higherDirectImage_of_proper_over_field
    {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : Y ⟶ X)
    [Proper (SchemeRealization.toBase X)] [Proper (SchemeRealization.toBase Y)]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    (𝒢 : Y.Modules) [𝒢.IsCoherent] :
    eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase Y) 𝒢 =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) *
          eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X)
            (Modules.higherDirectImage f 𝒢 i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
