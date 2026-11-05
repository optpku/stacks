/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality.ExplicitCore
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.Source
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal-Hom unit-to-endomorphism exact pairings
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory
noncomputable section
universe v u
namespace CategoryTheory.MonoidalClosed

/-- The tensor-to-endomorphism comparison selected by an explicit closed owner. -/
@[stacks 0FNY "explicit closed-owner tensor-to-endomorphism comparison"]
noncomputable def tensorIhomUnitToEndOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C) :
    X ⊗ (ihomOf H X).obj (𝟙_ C) ⟶ (ihomOf H X).obj X :=
  (β_ X ((ihomOf H X).obj (𝟙_ C))).hom ≫
    ((ihomOf H X).obj (𝟙_ C)) ◁
      (@unitIsoSelf C _ _ X (@MonoidalClosed.closed C _ _ H (𝟙_ C))).inv ≫
    @CategoryTheory.MonoidalClosed.comp C _ _ X (𝟙_ C) X
      (@MonoidalClosed.closed C _ _ H X)
      (@MonoidalClosed.closed C _ _ H (𝟙_ C))

/-- The explicit closed-owner tensor-to-endomorphism comparison unfolds to its braiding, unit
comparison, and enriched-composition composite. -/
@[stacks 0FNY "explicit tensor-to-endomorphism comparison specification"]
theorem tensorIhomUnitToEndOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C) :
    tensorIhomUnitToEndOf H X =
      (β_ X ((ihomOf H X).obj (𝟙_ C))).hom ≫
        ((ihomOf H X).obj (𝟙_ C)) ◁
          (@unitIsoSelf C _ _ X (@MonoidalClosed.closed C _ _ H (𝟙_ C))).inv ≫
        @CategoryTheory.MonoidalClosed.comp C _ _ X (𝟙_ C) X
          (@MonoidalClosed.closed C _ _ H X)
          (@MonoidalClosed.closed C _ _ H (𝟙_ C)) := rfl

/-- The explicit closed-owner tensor-to-endomorphism comparison is the source-order
tensor/internal-Hom comparison followed by the right unitor in its target. -/
@[stacks 0FNY "explicit tensor-to-endomorphism source-order formula"]
theorem tensorIhomUnitToEndOf_eq_sourceTensor
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C) :
    tensorIhomUnitToEndOf H X =
      @Source.tensor C _ _ _ H X (𝟙_ C) X ≫
        (ihomOf H X).map (ρ_ X).hom := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  change tensorIhomUnitToEnd X =
    Source.tensor X (𝟙_ C) X ≫ (ihom X).map (ρ_ X).hom
  exact CategoryTheory.MonoidalClosed.Dual.tensorIhomUnitToEnd_eq_sourceTensor X

/-- The inverse of the explicit closed-owner tensor-to-endomorphism comparison. -/
@[stacks 0FNY "explicit tensor-to-endomorphism comparison inverse"]
noncomputable def tensorIhomUnitToEndInvOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (ihomOf H X).obj X ⟶ X ⊗ (ihomOf H X).obj (𝟙_ C) :=
  CategoryTheory.inv (tensorIhomUnitToEndOf H X)

/-- The explicit closed-owner tensor-to-endomorphism comparison followed by its inverse is the
identity. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism forward-inverse law"]
theorem tensorIhomUnitToEndOf_hom_inv_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    tensorIhomUnitToEndOf H X ≫ tensorIhomUnitToEndInvOf H X = 𝟙 _ :=
  IsIso.hom_inv_id (tensorIhomUnitToEndOf H X)

/-- The inverse of the explicit closed-owner tensor-to-endomorphism comparison followed by the
comparison is the identity. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism inverse-forward law"]
theorem tensorIhomUnitToEndOf_inv_hom_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    tensorIhomUnitToEndInvOf H X ≫ tensorIhomUnitToEndOf H X = 𝟙 _ :=
  IsIso.inv_hom_id (tensorIhomUnitToEndOf H X)

/-- The explicit closed-owner tensor-to-endomorphism comparison packaged as an isomorphism. -/
@[stacks 0FNY "explicit tensor-to-endomorphism comparison isomorphism"]
noncomputable def tensorIhomUnitToEndIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    X ⊗ (ihomOf H X).obj (𝟙_ C) ≅ (ihomOf H X).obj X where
  hom := tensorIhomUnitToEndOf H X
  inv := tensorIhomUnitToEndInvOf H X
  hom_inv_id := tensorIhomUnitToEndOf_hom_inv_id H X
  inv_hom_id := tensorIhomUnitToEndOf_inv_hom_id H X

/-- The forward map of the explicit tensor-to-endomorphism isomorphism. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism isomorphism hom"]
theorem tensorIhomUnitToEndIsoOf_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (tensorIhomUnitToEndIsoOf H X).hom = tensorIhomUnitToEndOf H X := rfl

/-- The inverse map of the explicit tensor-to-endomorphism isomorphism. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism isomorphism inverse"]
theorem tensorIhomUnitToEndIsoOf_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (tensorIhomUnitToEndIsoOf H X).inv = tensorIhomUnitToEndInvOf H X := rfl

/-- The coevaluation associated with an explicit tensor-to-endomorphism inverse. -/
@[stacks 0FNY "explicit closed-owner internal-Hom coevaluation"]
noncomputable def ihomUnitCoevaluationOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    𝟙_ C ⟶ (ihomOf H X).obj (𝟙_ C) ⊗ X :=
  @curry' C _ _ X X (@MonoidalClosed.closed C _ _ H X) (𝟙 X) ≫
    tensorIhomUnitToEndInvOf H X ≫
      (β_ X ((ihomOf H X).obj (𝟙_ C))).hom

/-- The first triangle identity for the explicit-owner internal-Hom exact pairing. -/
@[stacks 0FNY "explicit internal-Hom pairing first triangle"]
theorem ihomUnitExactPairingOf_coevaluation_evaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    X ◁ ihomUnitCoevaluationOf H X ≫
        (α_ X ((ihomOf H X).obj (𝟙_ C)) X).inv ≫
          ((@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C)) ▷ X =
      (ρ_ X).hom ≫ (λ_ X).inv := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the chosen tensor/internal-Hom adjunction used by this proof.
  letI : MonoidalClosed C := H
  -- Local instance justification (proof-local temporary data): install the derived `IsIso` fact
  -- only for the tensor/internal-Hom pairing calculation in this proof.
  letI : IsIso (tensorIhomUnitToEnd X) := by
    change IsIso (tensorIhomUnitToEndOf H X)
    infer_instance
  change X ◁ ihomUnitCoevaluation X ≫
      (α_ X ((ihom X).obj (𝟙_ C)) X).inv ≫
        ((ihom.ev X).app (𝟙_ C)) ▷ X =
    (ρ_ X).hom ≫ (λ_ X).inv
  exact (@ihomUnitExactPairing C _ _ _ _ X _).coevaluation_evaluation'

/-- The second triangle identity for the explicit-owner internal-Hom exact pairing. -/
@[stacks 0FNY "explicit internal-Hom pairing second triangle"]
theorem ihomUnitExactPairingOf_evaluation_coevaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    ihomUnitCoevaluationOf H X ▷ ((ihomOf H X).obj (𝟙_ C)) ≫
        (α_ ((ihomOf H X).obj (𝟙_ C)) X ((ihomOf H X).obj (𝟙_ C))).hom ≫
          ((ihomOf H X).obj (𝟙_ C)) ◁
            (@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C) =
      (λ_ ((ihomOf H X).obj (𝟙_ C))).hom ≫
        (ρ_ ((ihomOf H X).obj (𝟙_ C))).inv := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the chosen tensor/internal-Hom adjunction used by this proof.
  letI : MonoidalClosed C := H
  -- Local instance justification (proof-local temporary data): install the derived `IsIso` fact
  -- only for the tensor/internal-Hom pairing calculation in this proof.
  letI : IsIso (tensorIhomUnitToEnd X) := by
    change IsIso (tensorIhomUnitToEndOf H X)
    infer_instance
  change ihomUnitCoevaluation X ▷ ((ihom X).obj (𝟙_ C)) ≫
      (α_ ((ihom X).obj (𝟙_ C)) X ((ihom X).obj (𝟙_ C))).hom ≫
        ((ihom X).obj (𝟙_ C)) ◁ (ihom.ev X).app (𝟙_ C) =
    (λ_ ((ihom X).obj (𝟙_ C))).hom ≫ (ρ_ ((ihom X).obj (𝟙_ C))).inv
  exact (@ihomUnitExactPairing C _ _ _ _ X _).evaluation_coevaluation'

/-- The exact pairing furnished by an explicit closed owner and an invertible
tensor-to-endomorphism comparison. -/
@[reducible, stacks 0FNY "explicit internal-Hom exact pairing"]
noncomputable def ihomUnitExactPairingOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    ExactPairing ((ihomOf H X).obj (𝟙_ C)) X where
  coevaluation' := ihomUnitCoevaluationOf H X
  evaluation' := (@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C)
  coevaluation_evaluation' := ihomUnitExactPairingOf_coevaluation_evaluation H X
  evaluation_coevaluation' := ihomUnitExactPairingOf_evaluation_coevaluation H X

/-- The coevaluation projection of the explicit-owner internal-Hom exact pairing. -/
@[simp, stacks 0FNY "explicit internal-Hom pairing coevaluation projection"]
theorem ihomUnitExactPairingOf_coevaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (ihomUnitExactPairingOf H X).coevaluation' =
      ihomUnitCoevaluationOf H X := rfl

/-- The evaluation projection of the explicit-owner internal-Hom exact pairing. -/
@[simp, stacks 0FNY "explicit internal-Hom pairing evaluation projection"]
theorem ihomUnitExactPairingOf_evaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (ihomUnitExactPairingOf H X).evaluation' =
      (@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C) := rfl

end CategoryTheory.MonoidalClosed
