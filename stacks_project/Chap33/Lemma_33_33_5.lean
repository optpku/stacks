/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.Pushforward

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/- Lemma 33.33.5: let `k` be a field, let `φ : Y ⟶ X` be a morphism of schemes proper over
`k`, and let `𝒢` be a coherent `𝒪_Y`-module. Then the Euler characteristic of `𝒢` on `Y` is the
alternating sum of the Euler characteristics on `X` of the higher direct images `R^i φ_* 𝒢`. -/
@[stacks 0BEK] #check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic_eq_finsum_higherDirectImage_of_proper_over_field :
    ∀ {k : Type u} [Field k]
      {X Y : Over (Spec (CommRingCat.of k))}
      (φ : Y ⟶ X)
      [hProperX : IsProper X.hom] [hProperY : IsProper Y.hom]
      (𝒢 : Y.left.Modules) [𝒢.IsCoherent],
      AlgebraicGeometry.Scheme.Hom.eulerCharacteristic Y.hom 𝒢 =
        ∑ᶠ i : ℕ,
          ((i : ℤ).negOnePow : ℤ) *
            AlgebraicGeometry.Scheme.Hom.eulerCharacteristic X.hom
              (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule
                φ.left.toShHom 𝒢 i))
