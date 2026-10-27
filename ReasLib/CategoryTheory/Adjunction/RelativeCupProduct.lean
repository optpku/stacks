/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor maps on right adjoints

For monoidal categories, the canonical tensor map on a right adjoint is already
`Functor.LaxMonoidal.μ`, supplied by `Adjunction.rightAdjointLaxMonoidal`.  This file adds the raw
`_of` bridge needed before the tensor operations and their comparison have been bundled into
monoidal structures.  The bridge assumes only a morphism family, not invertibility or coherence.
`TensorModel` additionally requires a comparison natural in both variables.  For monoidal left
adjoints, `TensorModel.ofMonoidal` uses the given monoidal comparison, and its cup product agrees
with the canonical right-adjoint lax-monoidal tensorator.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe vC vD uC uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- A right adjoint together with a left adjoint and a bifunctorial tensor comparison.
Only the two tensor bifunctors are needed at this level; associators and units are not required.
For actual monoidal functors, use `TensorModel.ofMonoidal` to obtain the comparison from the
monoidal structure rather than choosing a new family of isomorphisms. -/
@[stacks 0B68 "tensor-compatible adjunction model"]
structure TensorModel (R : D ⥤ C) (tensorC : C ⥤ C ⥤ C)
    (tensorD : D ⥤ D ⥤ D) where
  /-- The chosen left adjoint. -/
  left : C ⥤ D
  /-- The adjunction exhibiting `left` as a left adjoint of `R`. -/
  adjunction : left ⊣ R
  /-- The components of the bifunctorial tensor comparison on the left adjoint. -/
  comparison (X Y : C) :
    left.obj ((tensorC.obj X).obj Y) ≅
      (tensorD.obj (left.obj X)).obj (left.obj Y)
  /-- Naturality of the tensor comparison in the first variable. -/
  comparison_naturality_left {X X' : C} (f : X ⟶ X') (Y : C) :
    left.map ((tensorC.map f).app Y) ≫ (comparison X' Y).hom =
      (comparison X Y).hom ≫ (tensorD.map (left.map f)).app (left.obj Y)
  /-- Naturality of the tensor comparison in the second variable. -/
  comparison_naturality_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    left.map ((tensorC.obj X).map g) ≫ (comparison X Y').hom =
      (comparison X Y).hom ≫ (tensorD.obj (left.obj X)).map (left.map g)

/-- The adjoint-side composite defining a raw tensor map on a right adjoint. -/
@[stacks 0B68 "right-adjoint tensor map adjoint composite"]
noncomputable def rightAdjointTensorMapAdjointOf
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    L.obj ((tensorC.obj (R.obj X)).obj (R.obj Y)) ⟶ (tensorD.obj X).obj Y :=
  comparison (R.obj X) (R.obj Y) ≫
    (tensorD.map (adj.counit.app X)).app (L.obj (R.obj Y)) ≫
    (tensorD.obj X).map (adj.counit.app Y)

/-- The raw tensor map on a right adjoint obtained by transposing a tensor comparison and the two
adjunction counits.  Arguments follow tensor order: `X` precedes `Y` in both source and target. -/
@[stacks 0B68 "right-adjoint tensor map from a comparison"]
noncomputable def rightAdjointTensorMapOf
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (tensorC.obj (R.obj X)).obj (R.obj Y) ⟶ R.obj ((tensorD.obj X).obj Y) :=
  adj.homEquiv _ _
    (rightAdjointTensorMapAdjointOf adj tensorC tensorD comparison X Y)

/-- Transposing `rightAdjointTensorMapOf` back across the adjunction recovers its defining
adjoint-side composite. -/
@[stacks 0B68 "right-adjoint tensor map specification"]
theorem rightAdjointTensorMapOf_spec
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (adj.homEquiv ((tensorC.obj (R.obj X)).obj (R.obj Y))
        ((tensorD.obj X).obj Y)).symm
      (rightAdjointTensorMapOf adj tensorC tensorD comparison X Y) =
    rightAdjointTensorMapAdjointOf adj tensorC tensorD comparison X Y := sorry

/-! The names below are compatibility aliases for the raw right-adjoint tensor map.
They do not assert naturality or monoidal coherence of the input comparison.  `TensorModel`
provides the bifunctorial layer, and `TensorModel.ofMonoidal` provides its monoidal specialization.
-/

/-- The adjoint-side morphism underlying a relative derived cup product. -/
@[stacks 0B68 "relative cup-product adjoint map"]
noncomputable abbrev relativeDerivedCupProductAdjointMap
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    L.obj ((tensorC.obj (R.obj X)).obj (R.obj Y)) ⟶ (tensorD.obj X).obj Y :=
  rightAdjointTensorMapAdjointOf adj tensorC tensorD comparison X Y

/-- The raw relative derived cup-product composite associated to an adjunction and a comparison
family.  This compatibility alias imposes no naturality or coherence on the family;
`TensorModel.cupProduct` requires bifunctoriality. -/
@[stacks 0B68 "relative derived cup product"]
noncomputable abbrev relativeDerivedCupProduct
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (tensorC.obj (R.obj X)).obj (R.obj Y) ⟶ R.obj ((tensorD.obj X).obj Y) :=
  rightAdjointTensorMapOf adj tensorC tensorD comparison X Y

/-- Transposing the relative derived cup product recovers its pullback-side composite. -/
@[stacks 0B68 "relative derived cup-product specification"]
theorem relativeDerivedCupProduct_spec
    (adj : L ⊣ R) (tensorC : C ⥤ C ⥤ C) (tensorD : D ⥤ D ⥤ D)
    (comparison : ∀ X Y,
      L.obj ((tensorC.obj X).obj Y) ⟶ (tensorD.obj (L.obj X)).obj (L.obj Y))
    (X Y : D) :
    (adj.homEquiv ((tensorC.obj (R.obj X)).obj (R.obj Y)) ((tensorD.obj X).obj Y)).symm
        (adj.relativeDerivedCupProduct tensorC tensorD comparison X Y) =
      adj.relativeDerivedCupProductAdjointMap tensorC tensorD comparison X Y := sorry

namespace TensorModel

variable {tensorC : C ⥤ C ⥤ C} {tensorD : D ⥤ D ⥤ D}

/-- The comparison bundled as a natural isomorphism of curried bifunctors. -/
def comparisonNatIso (M : TensorModel R tensorC tensorD) :
    tensorC ⋙ (Functor.whiskeringRight C C D).obj M.left ≅
      M.left ⋙ tensorD ⋙ (Functor.whiskeringLeft C D D).obj M.left :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (M.comparison X)
      (fun g => M.comparison_naturality_right X g))
    (fun f => by
      ext Y
      exact M.comparison_naturality_left f Y)

@[simp]
theorem comparisonNatIso_hom_app_app (M : TensorModel R tensorC tensorD) (X Y : C) :
    (M.comparisonNatIso.hom.app X).app Y = (M.comparison X Y).hom := rfl

@[simp]
theorem comparisonNatIso_inv_app_app (M : TensorModel R tensorC tensorD) (X Y : C) :
    (M.comparisonNatIso.inv.app X).app Y = (M.comparison X Y).inv := rfl

/-- The adjoint-side morphism underlying the cup product of a tensor-compatible adjunction
model. -/
@[stacks 0B68 "modeled relative cup-product adjoint map"]
noncomputable abbrev cupProductAdjoint
    (M : TensorModel R tensorC tensorD) (X Y : D) :
    M.left.obj ((tensorC.obj (R.obj X)).obj (R.obj Y)) ⟶
      (tensorD.obj X).obj Y :=
  M.adjunction.relativeDerivedCupProductAdjointMap tensorC tensorD
    (fun A B => (M.comparison A B).hom) X Y

/-- The cup product selected by a tensor-compatible adjunction model. -/
@[stacks 0B68 "modeled relative cup product"]
noncomputable abbrev cupProduct
    (M : TensorModel R tensorC tensorD) (X Y : D) :
    (tensorC.obj (R.obj X)).obj (R.obj Y) ⟶
      R.obj ((tensorD.obj X).obj Y) :=
  M.adjunction.relativeDerivedCupProduct tensorC tensorD
    (fun A B => (M.comparison A B).hom) X Y

/-- The modeled cup product is characterized by its adjoint-side morphism. -/
@[stacks 0B68 "modeled relative cup-product specification"]
theorem cupProduct_spec (M : TensorModel R tensorC tensorD) (X Y : D) :
    (M.adjunction.homEquiv
        ((tensorC.obj (R.obj X)).obj (R.obj Y)) ((tensorD.obj X).obj Y)).symm
        (M.cupProduct X Y) =
      M.cupProductAdjoint X Y :=
  (M.adjunction.homEquiv _ _).symm_apply_apply _

section Monoidal

open MonoidalCategory

variable [MonoidalCategory C] [MonoidalCategory D]

/-- The bifunctorial tensor model obtained from the given monoidal structure on the left adjoint.
The comparison is the inverse of its tensorator, with no further choice of isomorphisms. -/
def ofMonoidal (adj : L ⊣ R) [L.Monoidal] :
    TensorModel R (curriedTensor C) (curriedTensor D) where
  left := L
  adjunction := adj
  comparison X Y := (Functor.Monoidal.μIso L X Y).symm
  comparison_naturality_left f Y :=
    (Functor.OplaxMonoidal.δ_natural_left L f Y).symm
  comparison_naturality_right X {_ _} g :=
    (Functor.OplaxMonoidal.δ_natural_right L X g).symm

@[simp]
theorem ofMonoidal_comparison_hom (adj : L ⊣ R) [L.Monoidal] (X Y : C) :
    ((ofMonoidal adj).comparison X Y).hom = Functor.OplaxMonoidal.δ L X Y := rfl

/-- The monoidal specialization is exactly the tensorator of mathlib's canonical lax monoidal
structure on the right adjoint.  The induced structure is local to this statement. -/
theorem cupProduct_ofMonoidal (adj : L ⊣ R) [L.Monoidal] (X Y : D) :
    (ofMonoidal adj).cupProduct X Y =
      letI := adj.rightAdjointLaxMonoidal
      Functor.LaxMonoidal.μ R X Y := by
  change adj.homEquiv _ _
      (Functor.OplaxMonoidal.δ L _ _ ≫
        (adj.counit.app X ▷ _) ≫ (_ ◁ adj.counit.app Y)) =
    adj.homEquiv _ _
      (Functor.OplaxMonoidal.δ L _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y))
  simp only [tensorHom_def]
  rfl

end Monoidal

end TensorModel

end CategoryTheory.Adjunction
