/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic

/-!
# Euler characteristics of proper pushforwards

This module relates Euler characteristics over a field to the higher direct
images along a morphism between proper schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

/-- The Euler characteristic of a coherent module on a proper scheme over a field is the
alternating sum of the Euler characteristics of its higher direct images along any morphism to
another proper scheme over that field. -/
@[stacks 0BEK]
theorem eulerCharacteristic_eq_finsum_higherDirectImage_of_proper_over_field
    {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (φ : Y ⟶ X)
    [hProperX : IsProper X.hom] [hProperY : IsProper Y.hom]
    (𝒢 : Y.left.Modules) [𝒢.IsCoherent] :
    Scheme.Hom.eulerCharacteristic Y.hom 𝒢 =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) *
          Scheme.Hom.eulerCharacteristic X.hom
            (RingedSpace.Hom.higherDirectImageModule φ.left.toShHom 𝒢 i) := sorry

end Hom

end AlgebraicGeometry.Scheme
