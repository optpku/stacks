/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Codimension
public import ReasLib.AlgebraicGeometry.BivariantClass.ComponentRestriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Reindex
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter
public import Mathlib.Algebra.Group.Pi.Lemmas

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Codimension

open BivariantClass

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]

/-- An operational class of degree `q` acts stratumwise on codimension-graded Chow groups. -/
def cap (D : X.hom.GenericDimensionStratification δ) (a q : ℤ)
    (c : BivariantClass δ (𝟙 X) q) : Codimension D a →+ Codimension D (a + q) :=
  AddMonoidHom.piMap fun n ↦
    let W := ComponentRestriction.over X (D.stratum n)
    let j := ComponentRestriction.ι X (D.stratum n)
    (@RelativeChow.castDegree S _ δ _ W
      (ComponentRestriction.locallyOfFiniteTypeOver X _) _ _ (sub_sub n a q)).comp
      (@BivariantClass.cap S _ δ _ X X _ _ (𝟙 X) q c W W
        (ComponentRestriction.locallyOfFiniteTypeOver X _)
        (ComponentRestriction.locallyOfFiniteTypeOver X _) j (𝟙 W) j
        (ComponentRestriction.locallyOfFiniteTypeι X _) IsPullback.of_id_snd (n - a))

/-- The component of an operational cap is the homogeneous cap on that stratum,
transported from degree `n - a - q` to `n - (a + q)`. -/
theorem cap_apply (D : X.hom.GenericDimensionStratification δ) (a q : ℤ)
    (c : BivariantClass δ (𝟙 X) q) (α : Codimension D a) (n : ℤ) :
    cap δ D a q c α n =
      @RelativeChow.castDegree S _ δ _ (ComponentRestriction.over X (D.stratum n))
        (ComponentRestriction.locallyOfFiniteTypeOver X _) _ _ (sub_sub n a q)
        (@BivariantClass.cap S _ δ _ X X _ _ (𝟙 X) q c
          (ComponentRestriction.over X (D.stratum n))
          (ComponentRestriction.over X (D.stratum n))
          (ComponentRestriction.locallyOfFiniteTypeOver X _)
          (ComponentRestriction.locallyOfFiniteTypeOver X _)
          (ComponentRestriction.ι X (D.stratum n)) (𝟙 _)
          (ComponentRestriction.ι X (D.stratum n))
          (ComponentRestriction.locallyOfFiniteTypeι X _) IsPullback.of_id_snd (n - a)
          (α n)) := sorry

/-- Rationalization of the operational cap on the full codimension group. -/
def capQ (D : X.hom.GenericDimensionStratification δ) (a q : ℤ)
    (c : BivariantClass δ (𝟙 X) q) :
    TensorProduct ℤ (Codimension D a) ℚ →ₗ[ℤ]
      TensorProduct ℤ (Codimension D (a + q)) ℚ :=
  TensorProduct.map (cap δ D a q c).toIntLinearMap LinearMap.id

/-- Rational operational cap acts on the Chow factor of a pure tensor. -/
theorem capQ_tmul (D : X.hom.GenericDimensionStratification δ) (a q : ℤ)
    (c : BivariantClass δ (𝟙 X) q) (α : Codimension D a) (r : ℚ) :
    capQ δ D a q c (TensorProduct.tmul ℤ α r) =
      TensorProduct.tmul ℤ (cap δ D a q c α) r := sorry

/-- The action of the degree-`i` Chern character is the rational Newton cap divided by `i!`.
This is the cap action of `ChernClass.Theory.characterComponent`. -/
def characterCap (D : X.hom.GenericDimensionStratification δ) (a : ℤ)
    (classes : ChernClass.Theory δ X.hom) (E : X.left.Modules)
    [E.IsFiniteLocallyFree] (i : ℕ) :
    TensorProduct ℤ (Codimension D a) ℚ →ₗ[ℤ]
      TensorProduct ℤ (Codimension D (a + (i : ℤ))) ℚ :=
  (TensorProduct.map LinearMap.id (LinearMap.mulRight ℤ ((i.factorial : ℚ)⁻¹))).comp
    (capQ δ D a (i : ℤ) (ChernPolynomial.Newton.value δ X.hom classes E i))

/-- The degree-`i` Chern-character cap multiplies the rational tensor factor by `1 / i!`. -/
theorem characterCap_tmul (D : X.hom.GenericDimensionStratification δ) (a : ℤ)
    (classes : ChernClass.Theory δ X.hom) (E : X.left.Modules)
    [E.IsFiniteLocallyFree] (i : ℕ) (α : Codimension D a) (r : ℚ) :
    characterCap δ D a classes E i (TensorProduct.tmul ℤ α r) =
      TensorProduct.tmul ℤ
        (cap δ D a (i : ℤ) (ChernPolynomial.Newton.value δ X.hom classes E i) α)
        (r * (i.factorial : ℚ)⁻¹) := sorry

end AlgebraicGeometry.ChowGroup.Codimension
