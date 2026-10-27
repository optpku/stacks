/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Theory

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]

/-- The degree-`i` Chern-character action on rational homogeneous Chow groups is
the Newton cap divided by `i!`, namely the action of `characterComponent`. -/
def characterCap (classes : Theory δ X.hom) (E : X.left.Modules)
    [E.IsFiniteLocallyFree] (i : ℕ) (k : ℤ) :
    TensorProduct ℤ (RelativeChow δ X k) ℚ →ₗ[ℤ]
      TensorProduct ℤ (RelativeChow δ X (k - (i : ℤ))) ℚ :=
  TensorProduct.map
    ((ChernPolynomial.Newton.value δ X.hom classes E i).cap
      (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd k).toIntLinearMap
    (LinearMap.mulRight ℤ ((i.factorial : ℚ)⁻¹))

/-- On pure tensors, the Chern-character action is the Newton cap with the
rational coefficient divided by `i!`. -/
theorem characterCap_tmul (classes : Theory δ X.hom) (E : X.left.Modules)
    [E.IsFiniteLocallyFree] (i : ℕ) (k : ℤ) (α : RelativeChow δ X k) (r : ℚ) :
    characterCap δ classes E i k (TensorProduct.tmul ℤ α r) =
      TensorProduct.tmul ℤ
        ((ChernPolynomial.Newton.value δ X.hom classes E i).cap
          (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd k α)
        (r * (i.factorial : ℚ)⁻¹) := sorry

end AlgebraicGeometry.ChernClass.Theory
