/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import ReasLib.CategoryTheory.Monoidal.Duality.Adjunction
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Duality.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for dualizable objects

A strong monoidal left adjoint satisfies the projection formula on every right-dualizable
object.  The exact-pairing statement is the data-level interface; the object-property statement
is the choice-free interface intended for geometric finiteness hypotheses.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} [L.Monoidal]

namespace ExactPairing

/-- The explicit projection-formula natural isomorphism associated to chosen right-duality data.
It is obtained by identifying the two left adjoints and conjugating that identification to their
right adjoints. -/
@[stacks 0E8I "exact-pairing natural isomorphism"]
noncomputable def projectionFormulaNatIso
    {X X' : C} (p : ExactPairing X X') (adj : L ⊣ R) :
    R ⋙ tensorLeft X ≅ tensorLeft (L.obj X) ⋙ R :=
  conjugateIsoEquiv
    (p.tensorLeftAdjunction.comp adj)
    (adj.comp ((p.map L).tensorLeftAdjunction))
    (Functor.Monoidal.commTensorLeft L X')

set_option backward.isDefEq.respectTransparency false in
/-- Each component of the exact-pairing isomorphism is the canonical projection-formula mate. -/
@[simp]
theorem projectionFormulaNatIso_hom_app
    {X X' : C} (p : ExactPairing X X') (adj : L ⊣ R) (Y : D) :
    (p.projectionFormulaNatIso adj).hom.app Y = adj.projectionFormulaMate X Y := by
  apply ((adj.comp (p.map L).tensorLeftAdjunction).homEquiv _ _).symm.injective
  change
    (L ⋙ tensorLeft (L.obj X')).map
          ((p.projectionFormulaNatIso adj).hom.app Y) ≫
        (adj.comp (p.map L).tensorLeftAdjunction).counit.app Y = _
  rw [projectionFormulaNatIso]
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  rw [Adjunction.comp_homEquiv]
  dsimp only [Functor.comp_obj]
  rw [Equiv.symm_trans_apply]
  simp only [Adjunction.projectionFormulaMate,
    Adjunction.projectionFormulaMateOf,
    ExactPairing.tensorLeftAdjunction, CategoryTheory.tensorLeftAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  simp only [Functor.id_obj, Functor.Monoidal.commTensorLeft_hom_app,
    tensorLeftHomEquiv, evaluation, Adjunction.comp_counit_app,
    Adjunction.mkOfHomEquiv_counit_app, Equiv.symm_mk, Equiv.coe_fn_mk,
    whiskerLeft_id, Category.id_comp, Functor.map_comp, Category.assoc,
    Functor.OplaxMonoidal.left_unitality, Adjunction.projectionFormulaMapOf, id_tensorHom]
  erw [Equiv.symm_apply_apply]
  let ε : L.obj (R.obj Y) ⟶ Y := adj.counit.app Y
  change
    Functor.LaxMonoidal.μ L X' (X ⊗ R.obj Y) ≫
        L.map (α_ X' X (R.obj Y)).inv ≫ L.map (p.evaluation' ▷ R.obj Y) ≫
        L.map (λ_ (R.obj Y)).hom ≫ ε =
      L.obj X' ◁ (Functor.OplaxMonoidal.δ L X (R.obj Y) ≫
        L.obj X ◁ ε) ≫
        (α_ (L.obj X') (L.obj X) Y).inv ≫ p.mapEvaluation L ▷ Y ≫ (λ_ Y).hom
  rw [mapEvaluation, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_inv,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    whisker_exchange_assoc, whisker_exchange_assoc, leftUnitor_naturality]

/-- The forward map of the exact-pairing projection-formula isomorphism is the canonical mate. -/
@[simp]
theorem projectionFormulaNatIso_hom
    {X X' : C} (p : ExactPairing X X') (adj : L ⊣ R) :
    (p.projectionFormulaNatIso adj).hom =
      adj.projectionFormulaMateNatTrans X := by
  ext Y
  exact p.projectionFormulaNatIso_hom_app adj Y

/-- The explicit left projection-formula natural isomorphism associated to chosen left-duality
data. -/
@[stacks 0E8I "left exact-pairing natural isomorphism"]
noncomputable def leftProjectionFormulaNatIso
    {X X' : C} (p : ExactPairing X' X) (adj : L ⊣ R) :
    R ⋙ tensorRight X ≅ tensorRight (L.obj X) ⋙ R :=
  conjugateIsoEquiv
    (p.tensorRightAdjunction.comp adj)
    (adj.comp ((p.map L).tensorRightAdjunction))
    (Functor.Monoidal.commTensorRight L X')

set_option backward.isDefEq.respectTransparency false in
/-- Each component of the left exact-pairing isomorphism is the canonical left mate. -/
@[simp]
theorem leftProjectionFormulaNatIso_hom_app
    {X X' : C} (p : ExactPairing X' X) (adj : L ⊣ R) (Y : D) :
    (p.leftProjectionFormulaNatIso adj).hom.app Y = adj.leftProjectionFormulaMate Y X := by
  apply ((adj.comp (p.map L).tensorRightAdjunction).homEquiv _ _).symm.injective
  change
    (L ⋙ tensorRight (L.obj X')).map
          ((p.leftProjectionFormulaNatIso adj).hom.app Y) ≫
        (adj.comp (p.map L).tensorRightAdjunction).counit.app Y = _
  rw [leftProjectionFormulaNatIso]
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_counit]
  rw [Adjunction.comp_homEquiv]
  dsimp only [Functor.comp_obj]
  rw [Equiv.symm_trans_apply]
  simp only [Adjunction.leftProjectionFormulaMate,
    Adjunction.leftProjectionFormulaMateOf,
    ExactPairing.tensorRightAdjunction, CategoryTheory.tensorRightAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  simp only [Functor.id_obj, Functor.Monoidal.commTensorRight_hom_app,
    tensorRightHomEquiv, evaluation, Adjunction.comp_counit_app,
    Adjunction.mkOfHomEquiv_counit_app, Equiv.symm_mk, Equiv.coe_fn_mk,
    id_whiskerRight, Category.id_comp, Functor.map_comp, Category.assoc,
    Functor.OplaxMonoidal.right_unitality, Adjunction.leftProjectionFormulaMapOf, tensorHom_id]
  erw [Equiv.symm_apply_apply]
  let ε : L.obj (R.obj Y) ⟶ Y := adj.counit.app Y
  change
    Functor.LaxMonoidal.μ L (R.obj Y ⊗ X) X' ≫
        L.map (α_ (R.obj Y) X X').hom ≫ L.map (R.obj Y ◁ p.evaluation') ≫
        L.map (ρ_ (R.obj Y)).hom ≫ ε =
      (Functor.OplaxMonoidal.δ L (R.obj Y) X ≫
        ε ▷ L.obj X) ▷ L.obj X' ≫
        (α_ Y (L.obj X) (L.obj X')).hom ≫ Y ◁ p.mapEvaluation L ≫ (ρ_ Y).hom
  rw [mapEvaluation, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_rightUnitor]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_inv,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

/-- The forward map of the exact-pairing left projection-formula isomorphism is the canonical
left mate. -/
@[simp]
theorem leftProjectionFormulaNatIso_hom
    {X X' : C} (p : ExactPairing X' X) (adj : L ⊣ R) :
    (p.leftProjectionFormulaNatIso adj).hom =
      adj.leftProjectionFormulaMateNatTrans X := by
  ext Y
  exact p.leftProjectionFormulaNatIso_hom_app adj Y

/-- For a strong monoidal left adjoint, the projection-formula mate at an object equipped with
an explicit right dual is an isomorphism. -/
@[stacks 0E8I "exact-pairing form"]
theorem isIso_projectionFormulaMate
    {X X' : C} (p : ExactPairing X X') (adj : L ⊣ R) (Y : D) :
    IsIso (adj.projectionFormulaMate X Y) := by
  rw [← p.projectionFormulaNatIso_hom_app adj Y]
  exact ((p.projectionFormulaNatIso adj).app Y).isIso_hom

/-- For a strong monoidal left adjoint, the left projection-formula mate at an object equipped
with an explicit left dual is an isomorphism. -/
@[stacks 0E8I "left exact-pairing form"]
theorem isIso_leftProjectionFormulaMate
    {X X' : C} (p : ExactPairing X' X) (adj : L ⊣ R) (Y : D) :
    IsIso (adj.leftProjectionFormulaMate Y X) := by
  rw [← p.leftProjectionFormulaNatIso_hom_app adj Y]
  exact ((p.leftProjectionFormulaNatIso adj).app Y).isIso_hom

end ExactPairing

namespace IsRightDualizable

/-- A strong monoidal left adjoint satisfies the projection formula at every right-dualizable
object. -/
@[stacks 0E8I "right-dualizable form"]
theorem isIso_projectionFormulaMate
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) (Y : D) :
    IsIso (adj.projectionFormulaMate X Y) := by
  obtain ⟨hX⟩ := hX
  exact hX.exact.isIso_projectionFormulaMate adj Y

/-- For a fixed right-dualizable object, the projection-formula mates form an invertible natural
transformation. -/
theorem isIso_projectionFormulaMateNatTrans
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) :
    IsIso (adj.projectionFormulaMateNatTrans X) := by
  haveI : ∀ Y : D, IsIso ((adj.projectionFormulaMateNatTrans X).app Y) :=
    fun Y ↦ hX.isIso_projectionFormulaMate adj Y
  exact NatIso.isIso_of_isIso_app _

/-- The functorial projection-formula isomorphism associated to a right-dualizable source-side
factor. -/
@[stacks 0E8I "right-dualizable natural isomorphism"]
noncomputable def projectionFormulaNatIso
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) :
    R ⋙ tensorLeft X ≅ tensorLeft (L.obj X) ⋙ R :=
  (Classical.choice hX).exact.projectionFormulaNatIso adj

/-- The chosen-dual construction has the canonical projection-formula mate as its forward map. -/
@[simp]
theorem projectionFormulaNatIso_hom
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R) :
    (hX.projectionFormulaNatIso adj).hom =
      adj.projectionFormulaMateNatTrans X := by
  exact (Classical.choice hX).exact.projectionFormulaNatIso_hom adj

end IsRightDualizable

namespace IsLeftDualizable

/-- A strong monoidal left adjoint satisfies the left projection formula at every left-dualizable
object. -/
@[stacks 0E8I "left-dualizable form"]
theorem isIso_leftProjectionFormulaMate
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) (Y : D) :
    IsIso (adj.leftProjectionFormulaMate Y X) := by
  obtain ⟨hX⟩ := hX
  exact hX.exact.isIso_leftProjectionFormulaMate adj Y

/-- For a fixed left-dualizable object, the left projection-formula mates form an invertible
natural transformation. -/
theorem isIso_leftProjectionFormulaMateNatTrans
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) :
    IsIso (adj.leftProjectionFormulaMateNatTrans X) := by
  haveI : ∀ Y : D, IsIso ((adj.leftProjectionFormulaMateNatTrans X).app Y) :=
    fun Y ↦ hX.isIso_leftProjectionFormulaMate adj Y
  exact NatIso.isIso_of_isIso_app _

/-- The functorial left projection-formula isomorphism associated to a left-dualizable
source-side factor. -/
@[stacks 0E8I "left-dualizable natural isomorphism"]
noncomputable def leftProjectionFormulaNatIso
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) :
    R ⋙ tensorRight X ≅ tensorRight (L.obj X) ⋙ R :=
  (Classical.choice hX).exact.leftProjectionFormulaNatIso adj

/-- The chosen-left-dual construction has the canonical left projection-formula mate as its
forward map. -/
@[simp]
theorem leftProjectionFormulaNatIso_hom
    {X : C} (hX : IsLeftDualizable X) (adj : L ⊣ R) :
    (hX.leftProjectionFormulaNatIso adj).hom =
      adj.leftProjectionFormulaMateNatTrans X := by
  exact (Classical.choice hX).exact.leftProjectionFormulaNatIso_hom adj

end IsLeftDualizable

end CategoryTheory
