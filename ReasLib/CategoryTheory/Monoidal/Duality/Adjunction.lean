module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact pairings and tensor-compatible adjunctions

This leaf owns the concrete constructions that pass between an explicit exact pairing and a
tensor-right adjunction. Comparison, uniqueness, and round-trip API live in
`CategoryTheory.Monoidal.Duality.Comparison`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false

namespace ExactPairing

/-- The tensor-right adjunction determined by explicit exact-pairing data. -/
def tensorRightAdjunction {X Y : C} (p : ExactPairing X Y) :
    tensorRight X ⊣ tensorRight Y :=
  @CategoryTheory.tensorRightAdjunction C _ _ X Y p

/-- The tensor-left adjunction determined by explicit exact-pairing data. -/
def tensorLeftAdjunction {X Y : C} (p : ExactPairing X Y) :
    tensorLeft Y ⊣ tensorLeft X :=
  @CategoryTheory.tensorLeftAdjunction C _ _ X Y p

/-- An exact pairing identifies morphisms from the tensor unit into `M ⊗ Y` with
morphisms from `X` into `M`.  This is the Hom-set form of right duality, with no closed
structure required. -/
def unitHomEquiv {X Y : C} (p : ExactPairing X Y) (M : C) :
    (𝟙_ C ⟶ M ⊗ Y) ≃ (X ⟶ M) :=
  (((λ_ X).symm.homCongr (Iso.refl M)).trans
    (p.tensorRightAdjunction.homEquiv (𝟙_ C) M)).symm

/-- The forward map of `unitHomEquiv` is adjunction uncurrying followed by removal of the
left tensor unit. -/
@[simp]
theorem unitHomEquiv_apply {X Y : C} (p : ExactPairing X Y) (M : C)
    (s : 𝟙_ C ⟶ M ⊗ Y) :
    p.unitHomEquiv M s =
      (λ_ X).inv ≫ (p.tensorRightAdjunction.homEquiv (𝟙_ C) M).symm s := by
  change
    (λ_ X).inv ≫
        (p.tensorRightAdjunction.homEquiv (𝟙_ C) M).symm s ≫ 𝟙 M = _
  simp

/-- The inverse of `unitHomEquiv` sends `f : X ⟶ M` to coevaluation followed by
`f ⊗ 𝟙 Y`. -/
@[simp]
theorem unitHomEquiv_symm_apply {X Y : C} (p : ExactPairing X Y) (M : C)
    (f : X ⟶ M) :
    (p.unitHomEquiv M).symm f = p.coevaluation' ≫ f ▷ Y := by
  change
    (((λ_ X).symm.homCongr (Iso.refl M)).trans
      (p.tensorRightAdjunction.homEquiv (𝟙_ C) M)) f = _
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]
  rw [tensorRightAdjunction]
  rw [CategoryTheory.tensorRightAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  change
    (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ p.coevaluation' ≫
        (α_ (𝟙_ C) X Y).inv ≫ ((λ_ X).hom ≫ f) ▷ Y =
      p.coevaluation' ≫ f ▷ Y
  monoidal

end ExactPairing

namespace Adjunction

variable {X Y : C}

/-- A tensor-right adjunction is compatible with tensoring on the left when its Hom-equivalence
commutes with left tensoring, with the associators required in a non-strict monoidal category. -/
@[stacks 0FFR "compatibility of the adjunction with left tensoring"]
def CompatibleWithLeftTensoring (adj : tensorRight X ⊣ tensorRight Y) : Prop :=
  ∀ ⦃W Z Z' : C⦄ (f : Z' ⊗ X ⟶ Z),
    adj.homEquiv (W ⊗ Z') (W ⊗ Z) ((α_ W Z' X).hom ≫ W ◁ f) =
      W ◁ adj.homEquiv Z' Z f ≫ (α_ W Z Y).inv

/-- The Hom-equivalence of a tensor-compatible tensor-right adjunction commutes with left
tensoring. -/
@[reassoc]
theorem CompatibleWithLeftTensoring.homEquiv_whiskerLeft
    {W Z Z' : C} {adj : tensorRight X ⊣ tensorRight Y}
    (hcompat : adj.CompatibleWithLeftTensoring) (f : Z' ⊗ X ⟶ Z) :
    adj.homEquiv (W ⊗ Z') (W ⊗ Z) ((α_ W Z' X).hom ≫ W ◁ f) =
      W ◁ adj.homEquiv Z' Z f ≫ (α_ W Z Y).inv :=
  hcompat f

/-- The coevaluation obtained from the unit of a tensor-right adjunction at the tensor unit. -/
def tensorRightCoevaluation (adj : tensorRight X ⊣ tensorRight Y) : 𝟙_ C ⟶ X ⊗ Y :=
  adj.homEquiv (𝟙_ C) X (λ_ X).hom

/-- The evaluation obtained from the counit of a tensor-right adjunction at the tensor unit. -/
def tensorRightEvaluation (adj : tensorRight X ⊣ tensorRight Y) : Y ⊗ X ⟶ 𝟙_ C :=
  (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv

/-- Computation of the coevaluation reconstructed from a tensor-right adjunction. -/
@[simp] theorem tensorRightCoevaluation_eq (adj : tensorRight X ⊣ tensorRight Y) :
    adj.tensorRightCoevaluation = adj.homEquiv (𝟙_ C) X (λ_ X).hom := rfl

/-- Computation of the evaluation reconstructed from a tensor-right adjunction. -/
@[simp] theorem tensorRightEvaluation_eq (adj : tensorRight X ⊣ tensorRight Y) :
    adj.tensorRightEvaluation = (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv := rfl

/-- Tensor compatibility gives the triangle identity on the right-dual object. -/
theorem tensorRightCoevaluation_evaluation (adj : tensorRight X ⊣ tensorRight Y)
    (hcompat : adj.CompatibleWithLeftTensoring) :
    Y ◁ adj.tensorRightCoevaluation ≫ (α_ Y X Y).inv ≫
        adj.tensorRightEvaluation ▷ Y =
      (ρ_ Y).hom ≫ (λ_ Y).inv := by
  rw [tensorRightCoevaluation, tensorRightEvaluation]
  have hc := hcompat (W := Y) (Z' := 𝟙_ C) (Z := X) (λ_ X).hom
  rw [← reassoc_of% hc]
  have hn := adj.homEquiv_naturality_right
    ((α_ Y (𝟙_ C) X).hom ≫ Y ◁ (λ_ X).hom)
    ((adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv)
  change
    adj.homEquiv (Y ⊗ 𝟙_ C) (𝟙_ C)
          (((α_ Y (𝟙_ C) X).hom ≫ Y ◁ (λ_ X).hom) ≫
            (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv) =
        adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)
            ((α_ Y (𝟙_ C) X).hom ≫ Y ◁ (λ_ X).hom) ≫
          (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv ▷ Y at hn
  rw [← hn]
  have hmon :
      (α_ Y (𝟙_ C) X).hom ≫ Y ◁ (λ_ X).hom =
        (ρ_ Y).hom ▷ X := by
    monoidal
  rw [hmon]
  have hl := adj.homEquiv_naturality_left (ρ_ Y).hom
    ((adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv)
  change
    adj.homEquiv (Y ⊗ 𝟙_ C) (𝟙_ C)
          ((ρ_ Y).hom ▷ X ≫
            (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv) =
        (ρ_ Y).hom ≫ adj.homEquiv Y (𝟙_ C)
          ((adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv) at hl
  rw [hl]
  rw [Equiv.apply_symm_apply]

/-- Tensor compatibility gives the triangle identity on the original object. -/
theorem tensorRightEvaluation_coevaluation (adj : tensorRight X ⊣ tensorRight Y)
    (hcompat : adj.CompatibleWithLeftTensoring) :
    adj.tensorRightCoevaluation ▷ X ≫ (α_ X Y X).hom ≫
        X ◁ adj.tensorRightEvaluation =
      (λ_ X).hom ≫ (ρ_ X).inv := by
  rw [tensorRightCoevaluation, tensorRightEvaluation]
  apply (adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C)).injective
  have hl := adj.homEquiv_naturality_left
    (adj.homEquiv (𝟙_ C) X (λ_ X).hom)
    ((α_ X Y X).hom ≫
      X ◁ (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv)
  change
    adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C)
          ((adj.homEquiv (𝟙_ C) X (λ_ X).hom ▷ X) ≫
            ((α_ X Y X).hom ≫
              X ◁ (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv)) =
        adj.homEquiv (𝟙_ C) X (λ_ X).hom ≫
          adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C)
            ((α_ X Y X).hom ≫
              X ◁ (adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv) at hl
  rw [hl]
  have hc := hcompat (W := X) (Z' := Y) (Z := 𝟙_ C)
    ((adj.homEquiv Y (𝟙_ C)).symm (λ_ Y).inv)
  rw [hc]
  rw [Equiv.apply_symm_apply]
  have hn := adj.homEquiv_naturality_right (λ_ X).hom (ρ_ X).inv
  change
    adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C)
          ((λ_ X).hom ≫ (ρ_ X).inv) =
        adj.homEquiv (𝟙_ C) X (λ_ X).hom ≫
          ((ρ_ X).inv ▷ Y) at hn
  rw [hn]
  congr 1
  monoidal

/-- A tensor-compatible tensor-right adjunction determines explicit exact-pairing data. -/
@[implicit_reducible] def toExactPairing (adj : tensorRight X ⊣ tensorRight Y)
    (hcompat : adj.CompatibleWithLeftTensoring) : ExactPairing X Y where
  coevaluation' := adj.tensorRightCoevaluation
  evaluation' := adj.tensorRightEvaluation
  coevaluation_evaluation' := tensorRightCoevaluation_evaluation adj hcompat
  evaluation_coevaluation' := tensorRightEvaluation_coevaluation adj hcompat

/-- The coevaluation field of the exact pairing reconstructed from an adjunction. -/
@[simp] theorem toExactPairing_coevaluation' (adj : tensorRight X ⊣ tensorRight Y)
    (hcompat : adj.CompatibleWithLeftTensoring) :
    (adj.toExactPairing hcompat).coevaluation' = adj.tensorRightCoevaluation := rfl

/-- The evaluation field of the exact pairing reconstructed from an adjunction. -/
@[simp] theorem toExactPairing_evaluation' (adj : tensorRight X ⊣ tensorRight Y)
    (hcompat : adj.CompatibleWithLeftTensoring) :
    (adj.toExactPairing hcompat).evaluation' = adj.tensorRightEvaluation := rfl

end Adjunction

end

end CategoryTheory


