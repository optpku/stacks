module

public import ReasLib.CategoryTheory.Adjunction.RightIso
public import ReasLib.CategoryTheory.Monoidal.Duality.Adjunction
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Basic
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Enrichment

/-!
# Right internal Homs out of dualizable objects

An exact pairing `ExactPairing X Y` identifies right tensoring by `Y` with every chosen right
internal-Hom functor out of `X`.  This is the functorial owner behind the familiar isomorphism
`M ⊗ Y ≅ hom(X, M)` and the invertibility of the composition transpose.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory Opposite
open scoped CategoryTheory.RightInternalHom

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false

namespace ExactPairing

/-- An exact pairing `ExactPairing X Y` identifies right tensoring by `Y` with a chosen right
internal-Hom functor out of `X`. -/
@[stacks 08DQ "tensor-dual/internal-Hom natural isomorphism"]
def rightInternalHomIso
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) :
    tensorRight Y ≅ H.hom.obj (op X) :=
  p.tensorRightAdjunction.rightAdjointUniq (H.adj₂.adj X)

/-- The component of `rightInternalHomIso` gives the functorial comparison
`M ⊗ Y ≅ hom(X, M)`. -/
abbrev rightInternalHomIsoApp
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) (M : C) :
    M ⊗ Y ≅ (X ⟶[H]ᵣ M) :=
  (p.rightInternalHomIso H).app M

private theorem tensorRightAdjunction_counit_app
    {X Y : C} (p : ExactPairing X Y) (M : C) :
    p.tensorRightAdjunction.counit.app M =
      (α_ M Y X).hom ≫ M ◁ p.evaluation' ≫ (ρ_ M).hom := by
  change
    (@CategoryTheory.tensorRightHomEquiv C _ _ (M ⊗ Y) X Y M p).symm
        (CategoryStruct.id (X := M ⊗ Y)) = _
  simp [CategoryTheory.tensorRightHomEquiv]
  change M ◁ p.evaluation' = M ◁ p.evaluation'
  rfl

/-- The inverse duality comparison followed by the duality counit is the evaluation of the
chosen right internal Hom. -/
@[reassoc]
theorem rightInternalHomIso_inv_app_ev
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) (M : C) :
    ((p.rightInternalHomIso H).inv.app M ▷ X) ≫
        p.tensorRightAdjunction.counit.app M = H.ev X M := by
  rw [rightInternalHomIso, Adjunction.rightAdjointUniq_inv_app]
  change
    (tensorRight X).map
          (((H.adj₂.adj X).rightAdjointUniq
            p.tensorRightAdjunction).hom.app M) ≫
        p.tensorRightAdjunction.counit.app M = _
  simpa only [RightInternalHom.ev, Functor.id_obj] using
    (Adjunction.rightAdjointUniq_hom_app_counit
      (H.adj₂.adj X) p.tensorRightAdjunction M)

section Braided

variable [BraidedCategory C]

@[simp]
private theorem braidedSwap_evaluation'
    {X Y : C} (p : ExactPairing X Y) :
    p.braidedSwap.evaluation' = (β_ X Y).hom ≫ p.evaluation' := rfl

@[reassoc]
private theorem braid_comp_aux (X Y L : C) :
    (X ◁ (β_ Y L).inv) ≫ (α_ X Y L).inv ≫
        ((β_ X Y).hom ▷ L) ≫ (β_ (Y ⊗ X) L).hom =
      (β_ X (L ⊗ Y)).hom ≫ (α_ L Y X).hom := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  rw [BraidedCategory.yang_baxter X Y L]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]
  rw [BraidedCategory.braiding_tensor_right_hom]
  simp

@[reassoc]
private theorem braid_evaluation
    {X Y : C} (p : ExactPairing X Y) (L : C) :
    (X ◁ (β_ Y L).inv) ≫ (α_ X Y L).inv ≫
        ((β_ X Y).hom ▷ L) ≫ (p.evaluation' ▷ L) ≫
          (λ_ L).hom =
      (β_ X (L ⊗ Y)).hom ≫ (α_ L Y X).hom ≫
        (L ◁ p.evaluation') ≫ (ρ_ L).hom := by
  have hunit :
      (β_ (𝟙_ C) L).hom ≫ (ρ_ L).hom = (λ_ L).hom := by
    rw [braiding_tensorUnit_left]
    simp
  rw [← hunit]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [braid_comp_aux_assoc]

/-- The left-adjoint comparison whose right-adjoint mate is the composition transpose. -/
noncomputable def compTransposeLeftIso
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) (L : C) :
    tensorRight Y ⋙ tensorRight L ≅ tensorRight (X ⟶[H]ᵣ L) :=
  (tensorRightTensor Y L).symm ≪≫
    (tensoringRight C).mapIso
      ((β_ Y L) ≪≫ (p.rightInternalHomIso H).app L)

/-- A right dual for `X` identifies tensoring by `X` after `hom(L,-)` with
`hom(hom(X,L),-)`. -/
noncomputable def compTransposeNatIso
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) (L : C) :
    H.hom.obj (op L) ⋙ tensorRight X ≅ H.hom.obj (op (X ⟶[H]ᵣ L)) :=
  Adjunction.rightAdjointIsoOfLeftIso
    (p.compTransposeLeftIso H L)
    (p.braidedSwap.tensorRightAdjunction.comp (H.adj₂.adj L))
    (H.adj₂.adj (X ⟶[H]ᵣ L))

/-- The component of `compTransposeNatIso`; its forward map is `compTranspose`. -/
noncomputable abbrev compTransposeIso
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) (L M : C) :
    ((L ⟶[H]ᵣ M) ⊗ X) ≅ ((X ⟶[H]ᵣ L) ⟶[H]ᵣ M) :=
  (p.compTransposeNatIso H L).app M

/-- The forward map of the duality isomorphism is the canonical composition transpose. -/
theorem compTransposeIso_hom
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) (L M : C) :
    (p.compTransposeIso H L M).hom = H.compTranspose X L M := by
  apply H.uncurry_injective
  rw [H.uncurry_compTranspose]
  change
    (tensorRight (X ⟶[H]ᵣ L)).map
          ((p.compTransposeNatIso H L).hom.app M) ≫
        H.ev (X ⟶[H]ᵣ L) M = _
  have hc := Adjunction.rightAdjointIsoOfLeftIso_hom_app_counit
    (p.compTransposeLeftIso H L)
    (p.braidedSwap.tensorRightAdjunction.comp (H.adj₂.adj L))
    (H.adj₂.adj (X ⟶[H]ᵣ L)) M
  have hc' :
      (tensorRight (X ⟶[H]ᵣ L)).map
            ((p.compTransposeNatIso H L).hom.app M) ≫
          H.ev (X ⟶[H]ᵣ L) M =
        (p.compTransposeLeftIso H L).inv.app
            ((H.hom.obj (op L) ⋙ tensorRight X).obj M) ≫
          (p.braidedSwap.tensorRightAdjunction.comp
            (H.adj₂.adj L)).counit.app M := by
    simpa only [compTransposeNatIso, RightInternalHom.ev,
      Functor.id_obj] using hc
  rw [hc']
  simp only [compTransposeLeftIso, Iso.trans_inv, Iso.app_inv,
    NatTrans.comp_app, Functor.mapIso_inv, Adjunction.comp_counit_app]
  simp only [Functor.flip_map_app, Functor.flip_obj_map,
    curriedTensor_obj_map, curriedTensor_map_app,
    Iso.symm_inv, tensorRightTensor_hom_app]
  rw [tensorRightAdjunction_counit_app]
  rw [braidedSwap_evaluation']
  rw [← p.rightInternalHomIso_inv_app_ev H L]
  have hr :
      (X ◁ (p.rightInternalHomIso H).inv.app L) ≫ (β_ X (L ⊗ Y)).hom =
        (β_ X (X ⟶[H]ᵣ L)).hom ≫
          ((p.rightInternalHomIso H).inv.app L ▷ X) := by
    exact BraidedCategory.braiding_naturality_right X
      ((p.rightInternalHomIso H).inv.app L)
  monoidal
  simp
  have hrN :
      (L ⟶[H]ᵣ M) ◁ (β_ X (X ⟶[H]ᵣ L)).hom ≫
          (L ⟶[H]ᵣ M) ◁
            ((p.rightInternalHomIso H).inv.app L ▷ X) =
        (L ⟶[H]ᵣ M) ◁
            (X ◁ (p.rightInternalHomIso H).inv.app L) ≫
          (L ⟶[H]ᵣ M) ◁ (β_ X (L ⊗ Y)).hom := by
    simpa only [MonoidalCategory.whiskerLeft_comp] using
      congrArg (fun f ↦ (L ⟶[H]ᵣ M) ◁ f) hr.symm
  have hbN :
      (L ⟶[H]ᵣ M) ◁ (X ◁ (β_ Y L).inv) ≫
          (L ⟶[H]ᵣ M) ◁ (α_ X Y L).inv ≫
            (L ⟶[H]ᵣ M) ◁ ((β_ X Y).hom ▷ L) ≫
              (L ⟶[H]ᵣ M) ◁ (p.evaluation' ▷ L) ≫
                (L ⟶[H]ᵣ M) ◁ (λ_ L).hom =
        (L ⟶[H]ᵣ M) ◁ (β_ X (L ⊗ Y)).hom ≫
          (L ⟶[H]ᵣ M) ◁ (α_ L Y X).hom ≫
            (L ⟶[H]ᵣ M) ◁ (L ◁ p.evaluation') ≫
              (L ⟶[H]ᵣ M) ◁ (ρ_ L).hom := by
    simpa only [MonoidalCategory.whiskerLeft_comp] using
      congrArg (fun f ↦ (L ⟶[H]ᵣ M) ◁ f)
        (p.braid_evaluation L)
  rw [reassoc_of% hrN]
  rw [tensorRightAdjunction_counit_app]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hbN]
  rfl

/-- The composition transpose out of an object with an explicit right dual is an isomorphism. -/
@[stacks 0G40 "dualizable form"]
theorem isIso_compTranspose
    {X Y : C} (p : ExactPairing X Y) (H : RightInternalHom C) (L M : C) :
    IsIso (H.compTranspose X L M) := by
  rw [← p.compTransposeIso_hom H L M]
  infer_instance

end Braided

end ExactPairing

namespace IsRightDualizable

section Braided

variable [BraidedCategory C]

/-- The composition transpose out of a right-dualizable object is an isomorphism, independently
of the chosen right internal-Hom structure. -/
@[stacks 0G40 "right-dualizable form"]
theorem isIso_compTranspose
    {X : C} (hX : IsRightDualizable X)
    (H : RightInternalHom C) (L M : C) :
    IsIso (H.compTranspose X L M) := by
  obtain ⟨hX⟩ := hX
  exact hX.exact.isIso_compTranspose H L M

end Braided

end IsRightDualizable

end

end CategoryTheory
