/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Balanced tensor products and isomorphic coefficients

Changing the middle coefficient monoid by an isomorphism does not change a balanced tensor
product.  This file constructs the comparison directly from the two defining coequalizers and
records its naturality in both bimodule variables.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory.Bimod.ChangeOfScalars

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private theorem tensorIso_balance_iff {R A B T : Mon C}
    (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T)
    {W : C} (k : P.X ⊗ Q.X ⟶ W) :
    ((P.X ◁ e.inv.hom ≫ P.actRight) ▷ Q.X) ≫ k =
        (α_ P.X B.X Q.X).hom ≫ (P.X ◁ Q.actLeft) ≫ k ↔
      (P.actRight ▷ Q.X) ≫ k =
        (α_ P.X A.X Q.X).hom ≫ (P.X ◁ (e.hom.hom ▷ Q.X ≫ Q.actLeft)) ≫ k := by
  have he : e.inv.hom ≫ e.hom.hom = 𝟙 B.X := by
    rw [← Mon.comp_hom', e.inv_hom_id, Mon.id_hom']
  constructor
  · intro h
    refine (cancel_epi ((P.X ◁ e.inv.hom) ▷ Q.X)).1 ?_
    rw [← comp_whiskerRight_assoc, h, associator_naturality_middle_assoc]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight, he]
    simp
  · intro h
    rw [comp_whiskerRight_assoc, h, associator_naturality_middle_assoc]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight, he]
    simp

variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {R A B T : Mon C}

set_option backward.isDefEq.respectTransparency false in
/-- The carrier map comparing balanced tensors after replacing the middle monoid `A` by an
isomorphic monoid `B`.  It is induced by the quotient map for the `A`-balanced tensor. -/
@[stacks 0FSA "balanced tensor comparison under a coefficient isomorphism"]
noncomputable def tensorIsoHomCarrier (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    (((Bimod.restrictRight R e.inv).obj P).tensorBimod Q).X ⟶
      (P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q)).X :=
  coequalizer.desc
    (coequalizer.π
      (P.actRight ▷ ((Bimod.restrictLeft e.hom T).obj Q).X)
      ((α_ P.X A.X ((Bimod.restrictLeft e.hom T).obj Q).X).hom ≫
        (P.X ◁ ((Bimod.restrictLeft e.hom T).obj Q).actLeft)))
    (by
      simp only [Category.assoc]
      apply (tensorIso_balance_iff e P Q _).mpr
      exact (coequalizer.condition
          (P.actRight ▷ ((Bimod.restrictLeft e.hom T).obj Q).X)
          ((α_ P.X A.X ((Bimod.restrictLeft e.hom T).obj Q).X).hom ≫
            (P.X ◁ ((Bimod.restrictLeft e.hom T).obj Q).actLeft))).trans
        (Category.assoc _ _ _))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse carrier map, induced by the quotient map for the `B`-balanced tensor. -/
@[stacks 0FSA "inverse balanced tensor comparison under a coefficient isomorphism"]
noncomputable def tensorIsoInvCarrier (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    (P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q)).X ⟶
      (((Bimod.restrictRight R e.inv).obj P).tensorBimod Q).X :=
  coequalizer.desc
    (coequalizer.π
      (((Bimod.restrictRight R e.inv).obj P).actRight ▷ Q.X)
      ((α_ ((Bimod.restrictRight R e.inv).obj P).X B.X Q.X).hom ≫
        (((Bimod.restrictRight R e.inv).obj P).X ◁ Q.actLeft)))
    (by
      simp only [Category.assoc]
      apply (tensorIso_balance_iff e P Q _).mp
      exact (coequalizer.condition
          (((Bimod.restrictRight R e.inv).obj P).actRight ▷ Q.X)
          ((α_ ((Bimod.restrictRight R e.inv).obj P).X B.X Q.X).hom ≫
            (((Bimod.restrictRight R e.inv).obj P).X ◁ Q.actLeft))).trans
        (Category.assoc _ _ _))

set_option backward.isDefEq.respectTransparency false in
/-- The forward comparison sends the defining quotient map to the quotient map. -/
@[reassoc (attr := simp)]
theorem π_tensorIsoHomCarrier (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    coequalizer.π
        (((Bimod.restrictRight R e.inv).obj P).actRight ▷ Q.X)
        ((α_ ((Bimod.restrictRight R e.inv).obj P).X B.X Q.X).hom ≫
          (((Bimod.restrictRight R e.inv).obj P).X ◁ Q.actLeft)) ≫
        tensorIsoHomCarrier e P Q =
      coequalizer.π
        (P.actRight ▷ ((Bimod.restrictLeft e.hom T).obj Q).X)
        ((α_ P.X A.X ((Bimod.restrictLeft e.hom T).obj Q).X).hom ≫
          (P.X ◁ ((Bimod.restrictLeft e.hom T).obj Q).actLeft)) :=
  coequalizer.π_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison also preserves the defining quotient map. -/
@[reassoc (attr := simp)]
theorem π_tensorIsoInvCarrier (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    coequalizer.π
        (P.actRight ▷ ((Bimod.restrictLeft e.hom T).obj Q).X)
        ((α_ P.X A.X ((Bimod.restrictLeft e.hom T).obj Q).X).hom ≫
          (P.X ◁ ((Bimod.restrictLeft e.hom T).obj Q).actLeft)) ≫
        tensorIsoInvCarrier e P Q =
      coequalizer.π
        (((Bimod.restrictRight R e.inv).obj P).actRight ▷ Q.X)
        ((α_ ((Bimod.restrictRight R e.inv).obj P).X B.X Q.X).hom ≫
          (((Bimod.restrictRight R e.inv).obj P).X ◁ Q.actLeft)) :=
  coequalizer.π_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The balanced-tensor comparison as a morphism of the outer `(R,T)`-bimodules. -/
@[stacks 0FSA "balanced tensor morphism under a coefficient isomorphism"]
noncomputable def tensorIsoHom (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    ((Bimod.restrictRight R e.inv).obj P).tensorBimod Q ⟶
      P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q) where
  hom := tensorIsoHomCarrier e P Q
  left_act_hom := by
    refine (cancel_epi ((MonoidalCategory.tensorLeft R.X).map
      (coequalizer.π _ _))).1 ?_
    change (R.X ◁ coequalizer.π _ _) ≫
        Bimod.TensorBimod.actLeft _ _ ≫ tensorIsoHomCarrier e P Q =
      (R.X ◁ coequalizer.π _ _) ≫
        (R.X ◁ tensorIsoHomCarrier e P Q) ≫ Bimod.TensorBimod.actLeft _ _
    slice_lhs 1 2 => rw [Bimod.TensorBimod.whiskerLeft_π_actLeft]
    simp only [Category.assoc]
    rw [π_tensorIsoHomCarrier,
      ← whiskerLeft_comp_assoc, π_tensorIsoHomCarrier,
      Bimod.TensorBimod.whiskerLeft_π_actLeft]
    rfl
  right_act_hom := by
    refine (cancel_epi ((MonoidalCategory.tensorRight T.X).map
      (coequalizer.π _ _))).1 ?_
    change (coequalizer.π _ _ ▷ T.X) ≫
        Bimod.TensorBimod.actRight _ _ ≫ tensorIsoHomCarrier e P Q =
      (coequalizer.π _ _ ▷ T.X) ≫
        (tensorIsoHomCarrier e P Q ▷ T.X) ≫ Bimod.TensorBimod.actRight _ _
    slice_lhs 1 2 => rw [Bimod.TensorBimod.π_tensor_id_actRight]
    simp only [Category.assoc]
    rw [π_tensorIsoHomCarrier,
      ← comp_whiskerRight_assoc, π_tensorIsoHomCarrier,
      Bimod.TensorBimod.π_tensor_id_actRight]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse balanced-tensor comparison as a morphism of outer bimodules. -/
@[stacks 0FSA "inverse balanced tensor morphism under a coefficient isomorphism"]
noncomputable def tensorIsoInv (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q) ⟶
      ((Bimod.restrictRight R e.inv).obj P).tensorBimod Q where
  hom := tensorIsoInvCarrier e P Q
  left_act_hom := by
    refine (cancel_epi ((MonoidalCategory.tensorLeft R.X).map
      (coequalizer.π _ _))).1 ?_
    change (R.X ◁ coequalizer.π _ _) ≫
        Bimod.TensorBimod.actLeft _ _ ≫ tensorIsoInvCarrier e P Q =
      (R.X ◁ coequalizer.π _ _) ≫
        (R.X ◁ tensorIsoInvCarrier e P Q) ≫ Bimod.TensorBimod.actLeft _ _
    slice_lhs 1 2 => rw [Bimod.TensorBimod.whiskerLeft_π_actLeft]
    simp only [Category.assoc]
    rw [π_tensorIsoInvCarrier,
      ← whiskerLeft_comp_assoc, π_tensorIsoInvCarrier,
      Bimod.TensorBimod.whiskerLeft_π_actLeft]
    rfl
  right_act_hom := by
    refine (cancel_epi ((MonoidalCategory.tensorRight T.X).map
      (coequalizer.π _ _))).1 ?_
    change (coequalizer.π _ _ ▷ T.X) ≫
        Bimod.TensorBimod.actRight _ _ ≫ tensorIsoInvCarrier e P Q =
      (coequalizer.π _ _ ▷ T.X) ≫
        (tensorIsoInvCarrier e P Q ▷ T.X) ≫ Bimod.TensorBimod.actRight _ _
    slice_lhs 1 2 => rw [Bimod.TensorBimod.π_tensor_id_actRight]
    simp only [Category.assoc]
    rw [π_tensorIsoInvCarrier,
      ← comp_whiskerRight_assoc, π_tensorIsoInvCarrier,
      Bimod.TensorBimod.π_tensor_id_actRight]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The two coefficient-change comparisons compose to the identity on the `B`-balanced tensor. -/
theorem tensorIsoHomInv (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    tensorIsoHom e P Q ≫ tensorIsoInv e P Q = 𝟙 _ := by
  apply Bimod.hom_ext
  change tensorIsoHomCarrier e P Q ≫ tensorIsoInvCarrier e P Q = 𝟙 _
  apply coequalizer.hom_ext
  simp only [π_tensorIsoHomCarrier_assoc, π_tensorIsoInvCarrier]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The two coefficient-change comparisons compose to the identity on the `A`-balanced tensor. -/
theorem tensorIsoInvHom (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    tensorIsoInv e P Q ≫ tensorIsoHom e P Q = 𝟙 _ := by
  apply Bimod.hom_ext
  change tensorIsoInvCarrier e P Q ≫ tensorIsoHomCarrier e P Q = 𝟙 _
  apply coequalizer.hom_ext
  simp only [π_tensorIsoInvCarrier_assoc, π_tensorIsoHomCarrier]
  exact (Category.comp_id _).symm

/-- Balanced tensor product is invariant under an isomorphism of its middle coefficient monoid. -/
@[stacks 0FSA "balanced tensor isomorphism under a coefficient isomorphism"]
noncomputable def tensorIso (e : A ≅ B) (P : Bimod R A) (Q : Bimod B T) :
    ((Bimod.restrictRight R e.inv).obj P).tensorBimod Q ≅
      P.tensorBimod ((Bimod.restrictLeft e.hom T).obj Q) where
  hom := tensorIsoHom e P Q
  inv := tensorIsoInv e P Q
  hom_inv_id := tensorIsoHomInv e P Q
  inv_hom_id := tensorIsoInvHom e P Q

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient-change tensor isomorphism is natural in its left bimodule. -/
theorem tensorIso_natural_left (e : A ≅ B) {P P' : Bimod R A} (f : P ⟶ P')
    (Q : Bimod B T) :
    Bimod.whiskerRight ((Bimod.restrictRight R e.inv).map f) Q ≫
        (tensorIso e P' Q).hom =
      (tensorIso e P Q).hom ≫
        Bimod.whiskerRight f ((Bimod.restrictLeft e.hom T).obj Q) := by
  apply Bimod.hom_ext
  dsimp only [Bimod.comp_hom', tensorIso, tensorIsoHom, Bimod.whiskerRight]
  apply coequalizer.hom_ext
  simp only [ι_colimMap_assoc, ι_colimMap, parallelPairHom_app_one,
    π_tensorIsoHomCarrier_assoc, π_tensorIsoHomCarrier]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient-change tensor isomorphism is natural in its right bimodule. -/
theorem tensorIso_natural_right (e : A ≅ B) (P : Bimod R A)
    {Q Q' : Bimod B T} (g : Q ⟶ Q') :
    Bimod.whiskerLeft ((Bimod.restrictRight R e.inv).obj P) g ≫
        (tensorIso e P Q').hom =
      (tensorIso e P Q).hom ≫
        Bimod.whiskerLeft P ((Bimod.restrictLeft e.hom T).map g) := by
  apply Bimod.hom_ext
  dsimp only [Bimod.comp_hom', tensorIso, tensorIsoHom, Bimod.whiskerLeft]
  apply coequalizer.hom_ext
  simp only [ι_colimMap_assoc, ι_colimMap, parallelPairHom_app_one,
    π_tensorIsoHomCarrier_assoc, π_tensorIsoHomCarrier]
  rfl

end CategoryTheory.Bimod.ChangeOfScalars

end
