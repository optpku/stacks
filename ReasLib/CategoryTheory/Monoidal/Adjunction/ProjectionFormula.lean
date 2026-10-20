/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for monoidal adjunctions

For a monoidal adjunction `L ⊣ R`, this file names both canonical projection-formula maps
`L (A ⊗ R X) ⟶ L A ⊗ X` and `L (R X ⊗ A) ⟶ X ⊗ L A`, together with their adjoint mates and
naturality APIs. Invertibility of a map and invertibility of its mate are recorded as distinct
properties; they are not equivalent for a general adjunction. The two tensor orientations remain
distinct outside braided categories.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.OplaxMonoidal

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- The projection-formula map built from an explicitly supplied tensor comparison for the
left adjoint. This form applies before the comparison has been bundled as an oplax monoidal
structure. -/
@[stacks 0E8I "right projection formula map from a tensor comparison"]
def projectionFormulaMapOf
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (X : C) (Y : D) :
    L.obj (X ⊗ R.obj Y) ⟶ L.obj X ⊗ Y :=
  tensorComparison X (R.obj Y) ≫
    (𝟙 (L.obj X) ⊗ₘ adj.counit.app Y)

/-- The right-handed adjoint mate
`X ⊗ R Y ⟶ R (L X ⊗ Y)` of a projection-formula map built from an explicit tensor
comparison. -/
@[stacks 0E8I "right projection formula mate from a tensor comparison"]
noncomputable def projectionFormulaMateOf
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (X : C) (Y : D) :
    X ⊗ R.obj Y ⟶ R.obj (L.obj X ⊗ Y) :=
  adj.homEquiv _ _ (adj.projectionFormulaMapOf tensorComparison X Y)

/-- The raw projection-formula mate associated to an objectwise tensor-comparison isomorphism.
No coherence is inferred from the family of isomorphisms; use `projectionFormulaMate` when the
comparison is bundled as monoidal functor data. -/
@[stacks 0E8I "right projection formula mate from an objectwise comparison isomorphism"]
noncomputable def projectionFormulaMateOfIso
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (X : C) (Y : D) :
    X ⊗ R.obj Y ⟶ R.obj (L.obj X ⊗ Y) :=
  adj.projectionFormulaMateOf (fun A B ↦ (tensorComparison A B).hom) X Y

/-- Transposing the mate built from objectwise tensor-comparison isomorphisms recovers the map
built from their forward morphisms. -/
@[simp]
theorem projectionFormulaMateOfIso_spec
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (X : C) (Y : D) :
    (adj.homEquiv (X ⊗ R.obj Y) (L.obj X ⊗ Y)).symm
        (adj.projectionFormulaMateOfIso tensorComparison X Y) =
      adj.projectionFormulaMapOf (fun A B ↦ (tensorComparison A B).hom) X Y := sorry

/-- Transposing `projectionFormulaMateOf` back across the adjunction recovers the explicit
projection-formula map. -/
@[simp]
theorem projectionFormulaMateOf_spec
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (X : C) (Y : D) :
    (adj.homEquiv (X ⊗ R.obj Y) (L.obj X ⊗ Y)).symm
        (adj.projectionFormulaMateOf tensorComparison X Y) =
      adj.projectionFormulaMapOf tensorComparison X Y := sorry

/-- The raw projection-formula mate is natural in its source-category argument whenever the
supplied tensor comparison is natural there. -/
@[reassoc]
theorem projectionFormulaMateOf_natural_left
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ {X X' : C} (f : X ⟶ X') (Y : C),
      L.map (f ⊗ₘ 𝟙 Y) ≫ tensorComparison X' Y =
        tensorComparison X Y ≫ (L.map f ⊗ₘ 𝟙 (L.obj Y)))
    {X X' : C} (f : X ⟶ X') (Y : D) :
    (f ⊗ₘ 𝟙 (R.obj Y)) ≫
        adj.projectionFormulaMateOf tensorComparison X' Y =
      adj.projectionFormulaMateOf tensorComparison X Y ≫
        R.map (L.map f ⊗ₘ 𝟙 Y) := sorry

/-- The raw projection-formula mate is natural in its target-category argument whenever the
supplied tensor comparison is natural there. -/
@[reassoc]
theorem projectionFormulaMateOf_natural_right
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y'),
      L.map (𝟙 X ⊗ₘ f) ≫ tensorComparison X Y' =
        tensorComparison X Y ≫ (𝟙 (L.obj X) ⊗ₘ L.map f))
    (X : C) {Y Y' : D} (f : Y ⟶ Y') :
    (𝟙 X ⊗ₘ R.map f) ≫
        adj.projectionFormulaMateOf tensorComparison X Y' =
      adj.projectionFormulaMateOf tensorComparison X Y ≫
        R.map (𝟙 (L.obj X) ⊗ₘ f) := sorry

/-- The raw projection-formula map is natural in its source-category argument whenever the
supplied tensor comparison is natural there. -/
@[reassoc]
theorem projectionFormulaMapOf_natural_left
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ {X X' : C} (f : X ⟶ X') (Y : C),
      L.map (f ⊗ₘ 𝟙 Y) ≫ tensorComparison X' Y =
        tensorComparison X Y ≫ (L.map f ⊗ₘ 𝟙 (L.obj Y)))
    {X X' : C} (f : X ⟶ X') (Y : D) :
    L.map (f ⊗ₘ 𝟙 (R.obj Y)) ≫
        adj.projectionFormulaMapOf tensorComparison X' Y =
      adj.projectionFormulaMapOf tensorComparison X Y ≫
        (L.map f ⊗ₘ 𝟙 Y) := sorry

/-- The raw projection-formula map is natural in its target-category argument whenever the
supplied tensor comparison is natural there. -/
@[reassoc]
theorem projectionFormulaMapOf_natural_right
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y'),
      L.map (𝟙 X ⊗ₘ f) ≫ tensorComparison X Y' =
        tensorComparison X Y ≫ (𝟙 (L.obj X) ⊗ₘ L.map f))
    (X : C) {Y Y' : D} (f : Y ⟶ Y') :
    L.map (𝟙 X ⊗ₘ R.map f) ≫
        adj.projectionFormulaMapOf tensorComparison X Y' =
      adj.projectionFormulaMapOf tensorComparison X Y ≫
        (𝟙 (L.obj X) ⊗ₘ f) := sorry

/-- The left projection-formula map built from an explicitly supplied tensor comparison for the
left adjoint. -/
@[stacks 0B53 "left projection formula map from a tensor comparison"]
def leftProjectionFormulaMapOf
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (X : D) (A : C) :
    L.obj (R.obj X ⊗ A) ⟶ X ⊗ L.obj A :=
  tensorComparison (R.obj X) A ≫
    (adj.counit.app X ⊗ₘ 𝟙 (L.obj A))

/-- The adjoint mate `R X ⊗ A ⟶ R (X ⊗ L A)` of a left projection-formula map built from an
explicit tensor comparison. This is the tensor order used in Stacks projection formulas. -/
@[stacks 0B53 "left projection formula mate from a tensor comparison"]
noncomputable def leftProjectionFormulaMateOf
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (X : D) (A : C) :
    R.obj X ⊗ A ⟶ R.obj (X ⊗ L.obj A) :=
  adj.homEquiv _ _ (adj.leftProjectionFormulaMapOf tensorComparison X A)

/-- The raw left projection-formula mate associated to an objectwise tensor-comparison
isomorphism. No coherence is inferred from the family of isomorphisms. -/
@[stacks 0B53 "left objectwise comparison bridge"]
noncomputable def leftProjectionFormulaMateOfIso
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (X : D) (A : C) :
    R.obj X ⊗ A ⟶ R.obj (X ⊗ L.obj A) :=
  adj.leftProjectionFormulaMateOf (fun U V ↦ (tensorComparison U V).hom) X A

/-- Transposing the left mate built from objectwise tensor-comparison isomorphisms recovers the
left map built from their forward morphisms. -/
@[simp]
theorem leftProjectionFormulaMateOfIso_spec
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (X : D) (A : C) :
    (adj.homEquiv (R.obj X ⊗ A) (X ⊗ L.obj A)).symm
        (adj.leftProjectionFormulaMateOfIso tensorComparison X A) =
      adj.leftProjectionFormulaMapOf (fun U V ↦ (tensorComparison U V).hom) X A := sorry

/-- Transposing `leftProjectionFormulaMateOf` back across the adjunction recovers the explicit
left projection-formula map. -/
@[simp]
theorem leftProjectionFormulaMateOf_spec
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (X : D) (A : C) :
    (adj.homEquiv (R.obj X ⊗ A) (X ⊗ L.obj A)).symm
        (adj.leftProjectionFormulaMateOf tensorComparison X A) =
      adj.leftProjectionFormulaMapOf tensorComparison X A := sorry

/-- The raw left projection-formula mate is natural in its target-category argument whenever the
supplied tensor comparison is natural in its first argument. -/
@[reassoc]
theorem leftProjectionFormulaMateOf_natural_left
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ {X X' : C} (f : X ⟶ X') (Y : C),
      L.map (f ⊗ₘ 𝟙 Y) ≫ tensorComparison X' Y =
        tensorComparison X Y ≫ (L.map f ⊗ₘ 𝟙 (L.obj Y)))
    {X X' : D} (f : X ⟶ X') (A : C) :
    (R.map f ⊗ₘ 𝟙 A) ≫
        adj.leftProjectionFormulaMateOf tensorComparison X' A =
      adj.leftProjectionFormulaMateOf tensorComparison X A ≫
        R.map (f ⊗ₘ 𝟙 (L.obj A)) := sorry

/-- The raw left projection-formula mate is natural in its source-category argument whenever the
supplied tensor comparison is natural in its second argument. -/
@[reassoc]
theorem leftProjectionFormulaMateOf_natural_right
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y'),
      L.map (𝟙 X ⊗ₘ f) ≫ tensorComparison X Y' =
        tensorComparison X Y ≫ (𝟙 (L.obj X) ⊗ₘ L.map f))
    (X : D) {A A' : C} (f : A ⟶ A') :
    (𝟙 (R.obj X) ⊗ₘ f) ≫
        adj.leftProjectionFormulaMateOf tensorComparison X A' =
      adj.leftProjectionFormulaMateOf tensorComparison X A ≫
        R.map (𝟙 X ⊗ₘ L.map f) := sorry

/-- The raw left projection-formula map is natural in its target-category argument whenever the
supplied tensor comparison is natural in its first argument. -/
@[reassoc]
theorem leftProjectionFormulaMapOf_natural_left
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ {X X' : C} (f : X ⟶ X') (Y : C),
      L.map (f ⊗ₘ 𝟙 Y) ≫ tensorComparison X' Y =
        tensorComparison X Y ≫ (L.map f ⊗ₘ 𝟙 (L.obj Y)))
    {X X' : D} (f : X ⟶ X') (A : C) :
    L.map (R.map f ⊗ₘ 𝟙 A) ≫
        adj.leftProjectionFormulaMapOf tensorComparison X' A =
      adj.leftProjectionFormulaMapOf tensorComparison X A ≫
        (f ⊗ₘ 𝟙 (L.obj A)) := sorry

/-- The raw left projection-formula map is natural in its source-category argument whenever the
supplied tensor comparison is natural in its second argument. -/
@[reassoc]
theorem leftProjectionFormulaMapOf_natural_right
    (tensorComparison : ∀ X Y : C,
      L.obj (X ⊗ Y) ⟶ L.obj X ⊗ L.obj Y)
    (hTensor : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y'),
      L.map (𝟙 X ⊗ₘ f) ≫ tensorComparison X Y' =
        tensorComparison X Y ≫ (𝟙 (L.obj X) ⊗ₘ L.map f))
    (X : D) {A A' : C} (f : A ⟶ A') :
    L.map (𝟙 (R.obj X) ⊗ₘ f) ≫
        adj.leftProjectionFormulaMapOf tensorComparison X A' =
      adj.leftProjectionFormulaMapOf tensorComparison X A ≫
        (𝟙 X ⊗ₘ L.map f) := sorry

variable [L.OplaxMonoidal]

/-- The canonical projection-formula morphism associated to a monoidal adjunction. -/
@[stacks 0E8I "right projection formula"]
def projectionFormulaMap (X : C) (Y : D) :
    L.obj (X ⊗ R.obj Y) ⟶ L.obj X ⊗ Y :=
  adj.projectionFormulaMapOf (fun A B ↦ δ L A B) X Y

/-- The bundled oplax-monoidal projection-formula map is the raw map associated to its tensor
comparison. -/
@[simp, stacks 0E8I "right projection formula map oplax bridge"]
theorem projectionFormulaMapOf_oplax (X : C) (Y : D) :
    adj.projectionFormulaMapOf (fun A B ↦ δ L A B) X Y =
      adj.projectionFormulaMap X Y := sorry

/-- The adjoint mate of the canonical oplax-monoidal projection-formula map. -/
@[stacks 0E8I "right projection formula mate"]
noncomputable def projectionFormulaMate (X : C) (Y : D) :
    X ⊗ R.obj Y ⟶ R.obj (L.obj X ⊗ Y) :=
  adj.projectionFormulaMateOf (fun A B ↦ δ L A B) X Y

/-- The bundled projection-formula mate is the raw mate associated to the oplax-monoidal tensor
comparison. -/
@[simp, stacks 0E8I "right projection formula mate oplax bridge"]
theorem projectionFormulaMateOf_oplax (X : C) (Y : D) :
    adj.projectionFormulaMateOf (fun A B ↦ δ L A B) X Y =
      adj.projectionFormulaMate X Y := sorry

/-- Transposing the canonical projection-formula mate recovers the canonical projection-formula
map. -/
@[simp]
theorem projectionFormulaMate_spec (X : C) (Y : D) :
    (adj.homEquiv (X ⊗ R.obj Y) (L.obj X ⊗ Y)).symm
        (adj.projectionFormulaMate X Y) =
      adj.projectionFormulaMap X Y := sorry

/-- The projection-formula mate is natural in its source-category argument. -/
@[reassoc]
theorem projectionFormulaMate_natural_left {X X' : C} (f : X ⟶ X') (Y : D) :
    (f ⊗ₘ 𝟙 (R.obj Y)) ≫ adj.projectionFormulaMate X' Y =
      adj.projectionFormulaMate X Y ≫ R.map (L.map f ⊗ₘ 𝟙 Y) := sorry

/-- The projection-formula mate is natural in its target-category argument. -/
@[reassoc]
theorem projectionFormulaMate_natural_right (X : C) {Y Y' : D} (f : Y ⟶ Y') :
    (𝟙 X ⊗ₘ R.map f) ≫ adj.projectionFormulaMate X Y' =
      adj.projectionFormulaMate X Y ≫ R.map (𝟙 (L.obj X) ⊗ₘ f) := sorry

/-- The projection-formula mate satisfies the naturality equation expressed through the maps of
the fixed-factor tensor functors. -/
@[stacks 0E8I "right projection formula mate naturality"]
theorem projectionFormulaMateNatTrans_naturality
    (X : C) {Y Y' : D} (f : Y ⟶ Y') :
    (R ⋙ tensorLeft X).map f ≫ adj.projectionFormulaMate X Y' =
      adj.projectionFormulaMate X Y ≫ (tensorLeft (L.obj X) ⋙ R).map f := sorry

/-- For a fixed source-side tensor factor, the canonical projection-formula mates form a natural
transformation in the target-category variable. -/
@[stacks 0E8I "right projection formula mate natural transformation"]
noncomputable def projectionFormulaMateNatTrans (X : C) :
    R ⋙ tensorLeft X ⟶ tensorLeft (L.obj X) ⋙ R where
  app Y := adj.projectionFormulaMate X Y
  naturality {_ _} f := adj.projectionFormulaMateNatTrans_naturality X f

/-- The component of `projectionFormulaMateNatTrans` is the canonical projection-formula mate. -/
@[simp, stacks 0E8I "right projection formula mate natural transformation component"]
theorem projectionFormulaMateNatTrans_app (X : C) (Y : D) :
    (adj.projectionFormulaMateNatTrans X).app Y = adj.projectionFormulaMate X Y := sorry

/-- The inverse of the fixed-factor projection-formula mate natural transformation.

The inverse is named independently of the `IsIso` typeclass so downstream constructions can use
the inverse component without unfolding an `Iso` or an implementation detail. -/
@[stacks 0E8I "right projection formula inverse natural transformation"]
noncomputable def projectionFormulaMateNatTransInv (X : C)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    tensorLeft (L.obj X) ⋙ R ⟶ R ⋙ tensorLeft X :=
  CategoryTheory.inv (adj.projectionFormulaMateNatTrans X)

/-- Naturality of the inverse fixed-factor projection-formula mate. -/
@[stacks 0E8I "right projection formula inverse naturality"]
theorem projectionFormulaMateNatTransInv_naturality (X : C)
    [IsIso (adj.projectionFormulaMateNatTrans X)] {Y Y' : D} (f : Y ⟶ Y') :
    (tensorLeft (L.obj X) ⋙ R).map f ≫
        (adj.projectionFormulaMateNatTransInv X).app Y' =
      (adj.projectionFormulaMateNatTransInv X).app Y ≫
        (R ⋙ tensorLeft X).map f := sorry

/-- The forward and inverse projection-formula mate natural transformations compose to the
identity. -/
@[simp, stacks 0E8I "right projection formula natural transformation forward-inverse law"]
theorem projectionFormulaMateNatTrans_comp_inv (X : C)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    adj.projectionFormulaMateNatTrans X ≫
        adj.projectionFormulaMateNatTransInv X = 𝟙 _ := sorry

/-- The inverse and forward projection-formula mate natural transformations compose to the
identity. -/
@[simp, stacks 0E8I "right projection formula natural transformation inverse-forward law"]
theorem projectionFormulaMateNatTrans_inv_comp (X : C)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    adj.projectionFormulaMateNatTransInv X ≫
        adj.projectionFormulaMateNatTrans X = 𝟙 _ := sorry

/-- A component of the inverse projection-formula mate natural transformation is the inverse
of the corresponding canonical mate. -/
@[simp, stacks 0E8I "right projection formula inverse natural transformation component"]
theorem projectionFormulaMateNatTransInv_app (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    (adj.projectionFormulaMateNatTransInv X).app Y =
      CategoryTheory.inv ((adj.projectionFormulaMateNatTrans X).app Y) := sorry

/-- The natural isomorphism induced by the fixed-factor projection-formula mate when all of its
components are invertible. -/
@[stacks 0E8I "right projection formula natural isomorphism"]
noncomputable def projectionFormulaNatIso (X : C)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    R ⋙ tensorLeft X ≅ tensorLeft (L.obj X) ⋙ R :=
  { hom := adj.projectionFormulaMateNatTrans X
    inv := adj.projectionFormulaMateNatTransInv X
    hom_inv_id := adj.projectionFormulaMateNatTrans_comp_inv X
    inv_hom_id := adj.projectionFormulaMateNatTrans_inv_comp X }

/-- The forward natural transformation of `projectionFormulaNatIso` is the canonical mate
natural transformation. -/
@[simp, stacks 0E8I "right projection formula natural isomorphism hom"]
theorem projectionFormulaNatIso_hom (X : C)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    (adj.projectionFormulaNatIso X).hom = adj.projectionFormulaMateNatTrans X := sorry

/-- The inverse natural transformation of `projectionFormulaNatIso` is explicit. -/
@[simp, stacks 0E8I "right projection formula natural isomorphism inv"]
theorem projectionFormulaNatIso_inv (X : C)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    (adj.projectionFormulaNatIso X).inv = adj.projectionFormulaMateNatTransInv X := sorry

/-- The forward component of `projectionFormulaNatIso` is the canonical projection-formula mate.
-/
@[simp, stacks 0E8I "right projection formula natural isomorphism hom app"]
theorem projectionFormulaNatIso_hom_app (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    (adj.projectionFormulaNatIso X).hom.app Y = adj.projectionFormulaMate X Y := sorry

/-- The inverse component of `projectionFormulaNatIso` is the named mate inverse. -/
@[simp, stacks 0E8I "right projection formula natural isomorphism inv app"]
theorem projectionFormulaNatIso_inv_app (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMateNatTrans X)] :
    (adj.projectionFormulaNatIso X).inv.app Y =
      (adj.projectionFormulaMateNatTransInv X).app Y := sorry

/-- The projection-formula morphism is natural in its source-category argument. -/
@[reassoc]
theorem projectionFormulaMap_natural_left {X X' : C} (f : X ⟶ X') (Y : D) :
    L.map (f ⊗ₘ 𝟙 (R.obj Y)) ≫ adj.projectionFormulaMap X' Y =
      adj.projectionFormulaMap X Y ≫ (L.map f ⊗ₘ 𝟙 Y) := sorry

/-- The projection-formula morphism is natural in its target-category argument. -/
@[reassoc]
theorem projectionFormulaMap_natural_right (X : C) {Y Y' : D} (g : Y ⟶ Y') :
    L.map (𝟙 X ⊗ₘ R.map g) ≫ adj.projectionFormulaMap X Y' =
      adj.projectionFormulaMap X Y ≫ (𝟙 (L.obj X) ⊗ₘ g) := sorry

/-- Every right-handed projection-formula map of the adjunction is invertible. -/
@[stacks 0E8I "right projection formula map property"]
class ProjectionFormulaMap : Prop where
  isIso (X : C) (Y : D) : IsIso (adj.projectionFormulaMap X Y)

/-- A right projection-formula map hypothesis is exposed at each pair of objects. -/
instance [adj.ProjectionFormulaMap] (X : C) (Y : D) :
    IsIso (adj.projectionFormulaMap X Y) :=
  ProjectionFormulaMap.isIso X Y

/-- The named inverse of a componentwise projection-formula map. -/
@[stacks 0E8I "right projection formula map inverse"]
noncomputable def projectionFormulaMapInv (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMap X Y)] :
    L.obj X ⊗ Y ⟶ L.obj (X ⊗ R.obj Y) :=
  CategoryTheory.inv (adj.projectionFormulaMap X Y)

/-- A right projection-formula map followed by its named inverse is the identity. -/
@[simp, stacks 0E8I "right projection formula map forward-inverse law"]
theorem projectionFormulaMap_comp_inv (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMap X Y)] :
    adj.projectionFormulaMap X Y ≫ adj.projectionFormulaMapInv X Y = 𝟙 _ := sorry

/-- The inverse of a right projection-formula map followed by the map is the identity. -/
@[simp, stacks 0E8I "right projection formula map inverse-forward law"]
theorem projectionFormulaMapInv_comp (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMap X Y)] :
    adj.projectionFormulaMapInv X Y ≫ adj.projectionFormulaMap X Y = 𝟙 _ := sorry

/-- The componentwise projection-formula map isomorphism, oriented as
`L X ⊗ Y ≅ L (X ⊗ R Y)`. -/
@[stacks 0E8I "right projection formula map isomorphism"]
noncomputable def projectionFormulaMapIso (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMap X Y)] :
    L.obj X ⊗ Y ≅ L.obj (X ⊗ R.obj Y) :=
  { hom := adj.projectionFormulaMapInv X Y
    inv := adj.projectionFormulaMap X Y
    hom_inv_id := adj.projectionFormulaMapInv_comp X Y
    inv_hom_id := adj.projectionFormulaMap_comp_inv X Y }

/-- The forward map of `projectionFormulaMapIso` is the named inverse of the canonical map. -/
@[simp, stacks 0E8I "right projection formula map isomorphism hom"]
theorem projectionFormulaMapIso_hom (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMap X Y)] :
    (adj.projectionFormulaMapIso X Y).hom = adj.projectionFormulaMapInv X Y := sorry

/-- The inverse map of `projectionFormulaMapIso` is the canonical projection-formula map. -/
@[simp, stacks 0E8I "right projection formula map isomorphism inv"]
theorem projectionFormulaMapIso_inv (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMap X Y)] :
    (adj.projectionFormulaMapIso X Y).inv = adj.projectionFormulaMap X Y := sorry

/-- The unit specialization of the projection-formula map, oriented as
`L (R Y) ≅ L (𝟙_ C) ⊗ Y`. -/
@[stacks 0E8I "unit specialization"]
noncomputable def unitProjectionFormulaMapIso [adj.ProjectionFormulaMap] (Y : D) :
    L.obj (R.obj Y) ≅ L.obj (𝟙_ C) ⊗ Y :=
  ((adj.projectionFormulaMapIso (𝟙_ C) Y) ≪≫
    L.mapIso (λ_ (R.obj Y))).symm

/-- A monoidal adjunction satisfies the right-handed projection formula when every canonical
mate `X ⊗ R Y ⟶ R (L X ⊗ Y)` is an isomorphism. -/
@[stacks 0E8I "right projection formula property"]
class ProjectionFormula : Prop where
  isIso (X : C) (Y : D) : IsIso (adj.projectionFormulaMate X Y)

/-- A right projection-formula hypothesis is exposed at each pair of objects. -/
@[stacks 0E8I "right projection formula mate component instance"]
instance [adj.ProjectionFormula] (X : C) (Y : D) :
    IsIso (adj.projectionFormulaMate X Y) :=
  ProjectionFormula.isIso X Y

/-- A right projection-formula hypothesis makes each fixed-factor mate natural transformation
invertible, so its natural isomorphism API needs no manually rebuilt instance. -/
@[stacks 0E8I "right projection formula natural transformation invertibility"]
noncomputable instance projectionFormulaMateNatTrans_isIso [adj.ProjectionFormula] (X : C) :
    IsIso (adj.projectionFormulaMateNatTrans X) := sorry

/-- The named inverse of a componentwise projection-formula mate. -/
@[stacks 0E8I "right projection formula mate inverse"]
noncomputable def projectionFormulaMateInv (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMate X Y)] :
    R.obj (L.obj X ⊗ Y) ⟶ X ⊗ R.obj Y :=
  CategoryTheory.inv (adj.projectionFormulaMate X Y)

/-- A projection-formula mate followed by its named inverse is the identity. -/
@[simp, stacks 0E8I "right projection formula mate forward-inverse law"]
theorem projectionFormulaMate_comp_inv (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMate X Y)] :
    adj.projectionFormulaMate X Y ≫ adj.projectionFormulaMateInv X Y = 𝟙 _ := sorry

/-- The inverse of a projection-formula mate followed by the mate is the identity. -/
@[simp, stacks 0E8I "right projection formula mate inverse-forward law"]
theorem projectionFormulaMateInv_comp (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMate X Y)] :
    adj.projectionFormulaMateInv X Y ≫ adj.projectionFormulaMate X Y = 𝟙 _ := sorry

/-- The inverse component of the mate natural transformation agrees with the named component
inverse. -/
@[simp, stacks 0E8I "right projection formula mate inverse component bridge"]
theorem projectionFormulaMateNatTransInv_app_eq_mateInv (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMateNatTrans X)]
    [IsIso (adj.projectionFormulaMate X Y)] :
    (adj.projectionFormulaMateNatTransInv X).app Y =
      adj.projectionFormulaMateInv X Y := sorry

/-- The componentwise right projection-formula isomorphism. -/
@[stacks 0E8I "right projection formula isomorphism"]
noncomputable def projectionFormulaIso (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMate X Y)] :
    X ⊗ R.obj Y ≅ R.obj (L.obj X ⊗ Y) :=
  { hom := adj.projectionFormulaMate X Y
    inv := adj.projectionFormulaMateInv X Y
    hom_inv_id := adj.projectionFormulaMate_comp_inv X Y
    inv_hom_id := adj.projectionFormulaMateInv_comp X Y }

/-- The forward map of `projectionFormulaIso` is the canonical mate. -/
@[simp, stacks 0E8I "right projection formula isomorphism hom"]
theorem projectionFormulaIso_hom (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMate X Y)] :
    (adj.projectionFormulaIso X Y).hom = adj.projectionFormulaMate X Y := sorry

/-- The inverse map of `projectionFormulaIso` is the named mate inverse. -/
@[simp, stacks 0E8I "right projection formula isomorphism inv"]
theorem projectionFormulaIso_inv (X : C) (Y : D)
    [IsIso (adj.projectionFormulaMate X Y)] :
    (adj.projectionFormulaIso X Y).inv = adj.projectionFormulaMateInv X Y := sorry

/-- The left-handed projection-formula morphism associated to a monoidal adjunction. -/
@[stacks 0E8I "left projection formula"]
def leftProjectionFormulaMap (X : D) (A : C) :
    L.obj (R.obj X ⊗ A) ⟶ X ⊗ L.obj A :=
  adj.leftProjectionFormulaMapOf (fun U V ↦ δ L U V) X A

/-- The bundled oplax-monoidal left projection-formula map is the raw map associated to its tensor
comparison. -/
@[simp, stacks 0B53 "left projection formula map oplax bridge"]
theorem leftProjectionFormulaMapOf_oplax (X : D) (A : C) :
    adj.leftProjectionFormulaMapOf (fun U V ↦ δ L U V) X A =
      adj.leftProjectionFormulaMap X A := sorry

/-- The adjoint mate of the canonical left projection-formula map. -/
@[stacks 0B53 "canonical left adjoint mate"]
noncomputable def leftProjectionFormulaMate (X : D) (A : C) :
    R.obj X ⊗ A ⟶ R.obj (X ⊗ L.obj A) :=
  adj.leftProjectionFormulaMateOf (fun U V ↦ δ L U V) X A

/-- The bundled left projection-formula mate is the raw mate associated to the oplax-monoidal
tensor comparison. -/
@[simp, stacks 0B53 "left projection formula mate oplax bridge"]
theorem leftProjectionFormulaMateOf_oplax (X : D) (A : C) :
    adj.leftProjectionFormulaMateOf (fun U V ↦ δ L U V) X A =
      adj.leftProjectionFormulaMate X A := sorry

/-- Transposing the canonical left projection-formula mate recovers the canonical left
projection-formula map. -/
@[simp]
theorem leftProjectionFormulaMate_spec (X : D) (A : C) :
    (adj.homEquiv (R.obj X ⊗ A) (X ⊗ L.obj A)).symm
        (adj.leftProjectionFormulaMate X A) =
      adj.leftProjectionFormulaMap X A := sorry

/-- The left projection-formula mate is natural in its target-category argument. -/
@[reassoc]
theorem leftProjectionFormulaMate_natural_left {X X' : D} (f : X ⟶ X') (A : C) :
    (R.map f ⊗ₘ 𝟙 A) ≫ adj.leftProjectionFormulaMate X' A =
      adj.leftProjectionFormulaMate X A ≫ R.map (f ⊗ₘ 𝟙 (L.obj A)) := sorry

/-- The left projection-formula mate is natural in its source-category argument. -/
@[reassoc]
theorem leftProjectionFormulaMate_natural_right (X : D) {A A' : C} (f : A ⟶ A') :
    (𝟙 (R.obj X) ⊗ₘ f) ≫ adj.leftProjectionFormulaMate X A' =
      adj.leftProjectionFormulaMate X A ≫ R.map (𝟙 X ⊗ₘ L.map f) := sorry

/-- The left projection-formula mate satisfies the naturality equation expressed through the maps
of the fixed-factor tensor functors. -/
@[stacks 0B53 "left projection formula mate naturality"]
theorem leftProjectionFormulaMateNatTrans_naturality
    {X X' : D} (f : X ⟶ X') (A : C) :
    (R ⋙ tensorRight A).map f ≫ adj.leftProjectionFormulaMate X' A =
      adj.leftProjectionFormulaMate X A ≫ (tensorRight (L.obj A) ⋙ R).map f := sorry

/-- For a fixed source-category tensor factor, the canonical left projection-formula mates form a
natural transformation in the target-category variable. -/
@[stacks 0B53 "left projection formula mate natural transformation"]
noncomputable def leftProjectionFormulaMateNatTrans (A : C) :
    R ⋙ tensorRight A ⟶ tensorRight (L.obj A) ⋙ R where
  app X := adj.leftProjectionFormulaMate X A
  naturality {_ _} f := adj.leftProjectionFormulaMateNatTrans_naturality f A

/-- The component of `leftProjectionFormulaMateNatTrans` is the canonical left projection-formula
mate. -/
@[simp, stacks 0B53 "left projection formula mate natural transformation component"]
theorem leftProjectionFormulaMateNatTrans_app (X : D) (A : C) :
    (adj.leftProjectionFormulaMateNatTrans A).app X =
      adj.leftProjectionFormulaMate X A := sorry

/-- The inverse of the fixed-factor left projection-formula mate natural transformation. -/
@[stacks 0B53 "left projection formula inverse natural transformation"]
noncomputable def leftProjectionFormulaMateNatTransInv (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    tensorRight (L.obj A) ⋙ R ⟶ R ⋙ tensorRight A :=
  CategoryTheory.inv (adj.leftProjectionFormulaMateNatTrans A)

/-- Naturality of the inverse fixed-factor left projection-formula mate. -/
@[stacks 0B53 "left projection formula inverse naturality"]
theorem leftProjectionFormulaMateNatTransInv_naturality (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] {X X' : D} (f : X ⟶ X') :
    (tensorRight (L.obj A) ⋙ R).map f ≫
        (adj.leftProjectionFormulaMateNatTransInv A).app X' =
      (adj.leftProjectionFormulaMateNatTransInv A).app X ≫
        (R ⋙ tensorRight A).map f := sorry

/-- The forward and inverse left projection-formula mate natural transformations compose to the
identity. -/
@[simp, stacks 0B53 "left projection formula natural transformation forward-inverse law"]
theorem leftProjectionFormulaMateNatTrans_comp_inv (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    adj.leftProjectionFormulaMateNatTrans A ≫
        adj.leftProjectionFormulaMateNatTransInv A = 𝟙 _ := sorry

/-- The inverse and forward left projection-formula mate natural transformations compose to the
identity. -/
@[simp, stacks 0B53 "left projection formula natural transformation inverse-forward law"]
theorem leftProjectionFormulaMateNatTrans_inv_comp (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    adj.leftProjectionFormulaMateNatTransInv A ≫
        adj.leftProjectionFormulaMateNatTrans A = 𝟙 _ := sorry

/-- A component of the inverse left projection-formula mate natural transformation is the
inverse of the corresponding canonical mate. -/
@[simp, stacks 0B53 "left projection formula inverse natural transformation component"]
theorem leftProjectionFormulaMateNatTransInv_app (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    (adj.leftProjectionFormulaMateNatTransInv A).app X =
      CategoryTheory.inv ((adj.leftProjectionFormulaMateNatTrans A).app X) := sorry

/-- The natural isomorphism induced by the fixed-factor left projection-formula mate when all of
its components are invertible. -/
@[stacks 0B53 "left projection formula natural isomorphism"]
noncomputable def leftProjectionFormulaNatIso (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    R ⋙ tensorRight A ≅ tensorRight (L.obj A) ⋙ R :=
  { hom := adj.leftProjectionFormulaMateNatTrans A
    inv := adj.leftProjectionFormulaMateNatTransInv A
    hom_inv_id := adj.leftProjectionFormulaMateNatTrans_comp_inv A
    inv_hom_id := adj.leftProjectionFormulaMateNatTrans_inv_comp A }

/-- The forward natural transformation of `leftProjectionFormulaNatIso` is canonical. -/
@[simp, stacks 0B53 "left projection formula natural isomorphism hom"]
theorem leftProjectionFormulaNatIso_hom (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    (adj.leftProjectionFormulaNatIso A).hom = adj.leftProjectionFormulaMateNatTrans A := sorry

/-- The inverse natural transformation of `leftProjectionFormulaNatIso` is explicit. -/
@[simp, stacks 0B53 "left projection formula natural isomorphism inv"]
theorem leftProjectionFormulaNatIso_inv (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    (adj.leftProjectionFormulaNatIso A).inv = adj.leftProjectionFormulaMateNatTransInv A := sorry

/-- The forward component of `leftProjectionFormulaNatIso` is the canonical left mate. -/
@[simp, stacks 0B53 "left projection formula natural isomorphism hom app"]
theorem leftProjectionFormulaNatIso_hom_app (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    (adj.leftProjectionFormulaNatIso A).hom.app X = adj.leftProjectionFormulaMate X A := sorry

/-- The inverse component of `leftProjectionFormulaNatIso` is the named left mate inverse. -/
@[simp, stacks 0B53 "left projection formula natural isomorphism inv app"]
theorem leftProjectionFormulaNatIso_inv_app (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)] :
    (adj.leftProjectionFormulaNatIso A).inv.app X =
      (adj.leftProjectionFormulaMateNatTransInv A).app X := sorry

/-- The left projection-formula morphism is natural in its target-category argument. -/
@[reassoc]
theorem leftProjectionFormulaMap_natural_left {X X' : D} (f : X ⟶ X') (A : C) :
    L.map (R.map f ⊗ₘ 𝟙 A) ≫ adj.leftProjectionFormulaMap X' A =
      adj.leftProjectionFormulaMap X A ≫ (f ⊗ₘ 𝟙 (L.obj A)) := sorry

/-- The left projection-formula morphism is natural in its source-category argument. -/
@[reassoc]
theorem leftProjectionFormulaMap_natural_right (X : D) {A A' : C} (f : A ⟶ A') :
    L.map (𝟙 (R.obj X) ⊗ₘ f) ≫ adj.leftProjectionFormulaMap X A' =
      adj.leftProjectionFormulaMap X A ≫ (𝟙 X ⊗ₘ L.map f) := sorry

/-- Every left-handed projection-formula map of the adjunction is invertible. -/
@[stacks 0E8I "left projection formula map property"]
class LeftProjectionFormulaMap : Prop where
  isIso (X : D) (A : C) : IsIso (adj.leftProjectionFormulaMap X A)

/-- A left projection-formula map hypothesis is exposed at each pair of objects. -/
instance [adj.LeftProjectionFormulaMap] (X : D) (A : C) :
    IsIso (adj.leftProjectionFormulaMap X A) :=
  LeftProjectionFormulaMap.isIso X A

/-- The named inverse of a left projection-formula map. -/
@[stacks 0B53 "left projection formula map inverse"]
noncomputable def leftProjectionFormulaMapInv (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMap X A)] :
    X ⊗ L.obj A ⟶ L.obj (R.obj X ⊗ A) :=
  CategoryTheory.inv (adj.leftProjectionFormulaMap X A)

/-- A left projection-formula map followed by its named inverse is the identity. -/
@[simp, stacks 0B53 "left projection formula map forward-inverse law"]
theorem leftProjectionFormulaMap_comp_inv (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMap X A)] :
    adj.leftProjectionFormulaMap X A ≫ adj.leftProjectionFormulaMapInv X A = 𝟙 _ := sorry

/-- The inverse of a left projection-formula map followed by the map is the identity. -/
@[simp, stacks 0B53 "left projection formula map inverse-forward law"]
theorem leftProjectionFormulaMapInv_comp (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMap X A)] :
    adj.leftProjectionFormulaMapInv X A ≫ adj.leftProjectionFormulaMap X A = 𝟙 _ := sorry

/-- The componentwise left projection-formula map isomorphism, oriented as
`X ⊗ L A ≅ L (R X ⊗ A)`. -/
@[stacks 0E8I "left projection formula map isomorphism"]
noncomputable def leftProjectionFormulaMapIso (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMap X A)] :
    X ⊗ L.obj A ≅ L.obj (R.obj X ⊗ A) :=
  { hom := adj.leftProjectionFormulaMapInv X A
    inv := adj.leftProjectionFormulaMap X A
    hom_inv_id := adj.leftProjectionFormulaMapInv_comp X A
    inv_hom_id := adj.leftProjectionFormulaMap_comp_inv X A }

/-- The forward map of `leftProjectionFormulaMapIso` is the named inverse map. -/
@[simp, stacks 0B53 "left projection formula map isomorphism hom"]
theorem leftProjectionFormulaMapIso_hom (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMap X A)] :
    (adj.leftProjectionFormulaMapIso X A).hom = adj.leftProjectionFormulaMapInv X A := sorry

/-- The inverse map of `leftProjectionFormulaMapIso` is the canonical left map. -/
@[simp, stacks 0B53 "left projection formula map isomorphism inv"]
theorem leftProjectionFormulaMapIso_inv (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMap X A)] :
    (adj.leftProjectionFormulaMapIso X A).inv = adj.leftProjectionFormulaMap X A := sorry

/-- The unit specialization of the left projection-formula map, oriented as
`L (R X) ≅ X ⊗ L (𝟙_ C)`. -/
@[stacks 0E8I "left unit specialization"]
noncomputable def leftUnitProjectionFormulaMapIso [adj.LeftProjectionFormulaMap] (X : D) :
    L.obj (R.obj X) ≅ X ⊗ L.obj (𝟙_ C) :=
  ((adj.leftProjectionFormulaMapIso X (𝟙_ C)) ≪≫
    L.mapIso (ρ_ (R.obj X))).symm

/-- A monoidal adjunction satisfies the left-handed projection formula when every canonical mate
`R X ⊗ A ⟶ R (X ⊗ L A)` is an isomorphism. -/
@[stacks 0B53 "left projection formula property"]
class LeftProjectionFormula : Prop where
  isIso (X : D) (A : C) : IsIso (adj.leftProjectionFormulaMate X A)

/-- A left projection-formula hypothesis is exposed at each pair of objects. -/
@[stacks 0B53 "left projection formula mate component instance"]
instance [adj.LeftProjectionFormula] (X : D) (A : C) :
    IsIso (adj.leftProjectionFormulaMate X A) :=
  LeftProjectionFormula.isIso X A

/-- A left projection-formula hypothesis makes each fixed-factor mate natural transformation
invertible, so its natural isomorphism API needs no manually rebuilt instance. -/
@[stacks 0B53 "left projection formula natural transformation invertibility"]
noncomputable instance leftProjectionFormulaMateNatTrans_isIso [adj.LeftProjectionFormula]
    (A : C) : IsIso (adj.leftProjectionFormulaMateNatTrans A) := sorry

/-- The named inverse of a left projection-formula mate. -/
@[stacks 0B53 "left projection formula mate inverse"]
noncomputable def leftProjectionFormulaMateInv (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMate X A)] :
    R.obj (X ⊗ L.obj A) ⟶ R.obj X ⊗ A :=
  CategoryTheory.inv (adj.leftProjectionFormulaMate X A)

/-- A left projection-formula mate followed by its named inverse is the identity. -/
@[simp, stacks 0B53 "left projection formula mate forward-inverse law"]
theorem leftProjectionFormulaMate_comp_inv (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMate X A)] :
    adj.leftProjectionFormulaMate X A ≫ adj.leftProjectionFormulaMateInv X A = 𝟙 _ := sorry

/-- The inverse of a left projection-formula mate followed by the mate is the identity. -/
@[simp, stacks 0B53 "left projection formula mate inverse-forward law"]
theorem leftProjectionFormulaMateInv_comp (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMate X A)] :
    adj.leftProjectionFormulaMateInv X A ≫ adj.leftProjectionFormulaMate X A = 𝟙 _ := sorry

/-- The inverse component of the left mate natural transformation agrees with the named
component inverse. -/
@[simp, stacks 0B53 "left projection formula mate inverse component bridge"]
theorem leftProjectionFormulaMateNatTransInv_app_eq_mateInv (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMateNatTrans A)]
    [IsIso (adj.leftProjectionFormulaMate X A)] :
    (adj.leftProjectionFormulaMateNatTransInv A).app X =
      adj.leftProjectionFormulaMateInv X A := sorry

/-- The componentwise left projection-formula isomorphism. -/
@[stacks 0B53 "left projection formula isomorphism"]
noncomputable def leftProjectionFormulaIso (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMate X A)] :
    R.obj X ⊗ A ≅ R.obj (X ⊗ L.obj A) :=
  { hom := adj.leftProjectionFormulaMate X A
    inv := adj.leftProjectionFormulaMateInv X A
    hom_inv_id := adj.leftProjectionFormulaMate_comp_inv X A
    inv_hom_id := adj.leftProjectionFormulaMateInv_comp X A }

/-- The forward map of `leftProjectionFormulaIso` is the canonical left mate. -/
@[simp, stacks 0B53 "left projection formula isomorphism hom"]
theorem leftProjectionFormulaIso_hom (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMate X A)] :
    (adj.leftProjectionFormulaIso X A).hom = adj.leftProjectionFormulaMate X A := sorry

/-- The inverse map of `leftProjectionFormulaIso` is the named left mate inverse. -/
@[simp, stacks 0B53 "left projection formula isomorphism inv"]
theorem leftProjectionFormulaIso_inv (X : D) (A : C)
    [IsIso (adj.leftProjectionFormulaMate X A)] :
    (adj.leftProjectionFormulaIso X A).inv = adj.leftProjectionFormulaMateInv X A := sorry

end CategoryTheory.Adjunction
