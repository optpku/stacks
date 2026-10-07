module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associativity of fixed-right derived tensoring

@stack 0BYJ

The derived tensor associator is concrete only after an ambient fixed-right model is supplied.
This leaf owns that model-parametrized comparison and its naturality in all three factors; it does
not install a monoidal structure on a derived category or hide one behind a local instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Right

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ K L : CochainComplex C ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [MonoidalCategory (DerivedCategory C)]
variable [Has (C := C)]

local notation "D" => DerivedCategory C

/-- Lemma 15.59.15 (0BYJ): successive fixed-right derived tensor functors are identified with
tensoring by the derived tensor of their two fixed factors, relative to `T`. -/
@[stacks 0BYJ "model-parametrized derived tensor associativity"]
noncomputable def tensorAssoc
    (T : Monoidal.Model (C := C)) (L M : D) :
    functor L ⋙ functor M ≅ functor (obj L M) :=
  Functor.isoWhiskerRight (T.tensorRightIsoFunctor L).symm
      (functor M) ≪≫
    Functor.isoWhiskerLeft ((tensoringRight D).obj L)
      (T.tensorRightIsoFunctor M).symm ≪≫
    (tensorRightTensor L M).symm ≪≫
    (tensoringRight D).mapIso (T.tensorIsoObj L M) ≪≫
    T.tensorRightIsoFunctor (obj L M)

/-- The objectwise form of `tensorAssoc`, with the source order matching iterated derived tensoring. -/
@[stacks 0BYJ, stacks 0FNQ "objectwise derived tensor associativity"]
noncomputable abbrev assoc
    (T : Monoidal.Model (C := C)) (K L M : D) :
    obj (obj K L) M ≅ obj K (obj L M) :=
  (tensorAssoc T L M).app K

set_option backward.isDefEq.respectTransparency false in
/-- The forward derived associator is the ambient associator conjugated by the fixed-right model
comparisons.  This is the normal form used by parameter-naturality proofs. -/
@[reassoc, stacks 0BYJ "derived tensor associator model specification"]
theorem assoc_hom_objIsoTensor
    (T : Monoidal.Model (C := C)) (K L M : D) :
    (assoc T K L M).hom ≫
        (T.functorIsoTensorRight ((functor M).obj L)).hom.app K =
      (T.functorIsoTensorRight M).hom.app ((functor L).obj K) ≫
        ((tensoringRight D).obj M).map
            ((T.functorIsoTensorRight L).hom.app K) ≫
          (α_ K L M).hom ≫
            ((tensoringRight D).map (T.objIsoTensor L M).inv).app K := by
  change (tensorAssoc T L M).hom.app K ≫
      (T.functorIsoTensorRight (obj L M)).hom.app K = _
  dsimp only [tensorAssoc]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapIso_hom, tensorRightTensor_inv_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [(T.tensorRightIsoFunctor M).inv.naturality_assoc
    ((T.tensorRightIsoFunctor L).inv.app K)]
  rfl

/-- The model-parametrized associator is natural in its left object. -/
@[reassoc, stacks 0BYJ "naturality of derived tensor associativity"]
theorem assoc_hom_naturality
    (T : Monoidal.Model (C := C))
    {K₁ K₂ : D} (f : K₁ ⟶ K₂) (L M : D) :
    (functor M).map ((functor L).map f) ≫
      (assoc T K₂ L M).hom =
    (assoc T K₁ L M).hom ≫
      (functor (obj L M)).map f :=
  (tensorAssoc T L M).hom.naturality f

/-- The inverse model-parametrized associator is natural in its left object. -/
@[reassoc, stacks 0BYJ "inverse naturality of derived tensor associativity"]
theorem assoc_inv_naturality
    (T : Monoidal.Model (C := C))
    {K₁ K₂ : D} (f : K₁ ⟶ K₂) (L M : D) :
    (functor (obj L M)).map f ≫
      (assoc T K₂ L M).inv =
      (assoc T K₁ L M).inv ≫
      (functor M).map ((functor L).map f) :=
  (tensorAssoc T L M).inv.naturality f

section Closed

variable [BraidedCategory (DerivedCategory C)]

set_option backward.isDefEq.respectTransparency false in
/-- The model-parametrized associator is natural in its middle object for the parameter map
selected by `H` and `T`. -/
@[reassoc, stacks 0BYJ "middle naturality of derived tensor associativity"]
theorem assoc_hom_naturality_middle
    (H : MonoidalClosed D)
    (T : Monoidal.Model (C := C))
    (K : D) {L₁ L₂ : D} (f : L₁ ⟶ L₂) (M : D) :
    (functor M).map ((Closed.tensorMapOf H T f).app K) ≫
        (assoc T K L₂ M).hom =
      (assoc T K L₁ M).hom ≫
        (Closed.tensorMapOf H T ((functor M).map f)).app K := by
  apply (cancel_mono
    ((T.functorIsoTensorRight ((functor M).obj L₂)).hom.app K)).1
  have hmap :
      (Closed.tensorMapOf H T ((functor M).map f)).app K ≫
          (T.functorIsoTensorRight ((functor M).obj L₂)).hom.app K =
        (T.functorIsoTensorRight ((functor M).obj L₁)).hom.app K ≫
          (K ◁ (functor M).map f) :=
    by
      simpa only [Monoidal.Model.objIsoTensor_hom,
        MonoidalCategory.id_tensorHom] using
        Closed.tensorMapOf_objIsoTensor H T ((functor M).map f) K
  have hf :
      (Closed.tensorMapOf H T f).app K ≫
          (T.functorIsoTensorRight L₂).hom.app K =
        (T.functorIsoTensorRight L₁).hom.app K ≫ K ◁ f :=
    by
      simpa only [Monoidal.Model.objIsoTensor_hom,
        MonoidalCategory.id_tensorHom] using
        Closed.tensorMapOf_objIsoTensor H T f K
  have hinv :
      f ▷ M ≫ (T.objIsoTensor L₂ M).inv =
        (T.objIsoTensor L₁ M).inv ≫ (functor M).map f :=
    by
      simpa only [MonoidalCategory.tensorHom_id] using
        T.objIsoTensor_inv_naturality M f
  simp only [Category.assoc]
  rw [hmap]
  conv_rhs =>
    rw [← Category.assoc, assoc_hom_objIsoTensor]
  rw [assoc_hom_objIsoTensor]
  rw [(T.functorIsoTensorRight M).hom.naturality_assoc
    ((Closed.tensorMapOf H T f).app K)]
  simp only [Category.assoc]
  apply (cancel_epi
    ((T.functorIsoTensorRight M).hom.app ((functor L₁).obj K))).2
  rw [← ((tensoringRight D).obj M).map_comp_assoc]
  rw [hf]
  rw [((tensoringRight D).obj M).map_comp_assoc]
  apply (cancel_epi (((tensoringRight D).obj M).map
    ((T.functorIsoTensorRight L₁).hom.app K))).2
  change (K ◁ f) ▷ M ≫ (α_ K L₂ M).hom ≫
      K ◁ (T.objIsoTensor L₂ M).inv =
    (α_ K L₁ M).hom ≫ K ◁ (T.objIsoTensor L₁ M).inv ≫
      K ◁ (functor M).map f
  rw [MonoidalCategory.associator_naturality_middle_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp, hinv]

/-- The inverse model-parametrized associator is natural in its middle object for the parameter
map selected by `H` and `T`. -/
@[reassoc, stacks 0BYJ "inverse middle naturality of derived tensor associativity"]
theorem assoc_inv_naturality_middle
    (H : MonoidalClosed D)
    (T : Monoidal.Model (C := C))
    (K : D) {L₁ L₂ : D} (f : L₁ ⟶ L₂) (M : D) :
    (Closed.tensorMapOf H T ((functor M).map f)).app K ≫
        (assoc T K L₂ M).inv =
      (assoc T K L₁ M).inv ≫
        (functor M).map ((Closed.tensorMapOf H T f).app K) := by
  rw [Iso.comp_inv_eq (assoc T K L₂ M), Category.assoc,
    Iso.eq_inv_comp (assoc T K L₁ M)]
  exact (assoc_hom_naturality_middle H T K f M).symm

set_option backward.isDefEq.respectTransparency false in
/-- The model-parametrized associator is natural in its right object for the parameter map
selected by `H` and `T`. -/
@[reassoc, stacks 0BYJ "right naturality of derived tensor associativity"]
theorem assoc_hom_naturality_right
    (H : MonoidalClosed D)
    (T : Monoidal.Model (C := C))
    (K L : D) {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (Closed.tensorMapOf H T f).app
          (obj K L) ≫
        (assoc T K L M₂).hom =
      (assoc T K L M₁).hom ≫
        (Closed.tensorMapOf H T
          ((Closed.tensorMapOf H T f).app L)).app K := by
  let g := (Closed.tensorMapOf H T f).app L
  have houter :
      (Closed.tensorMapOf H T f).app (obj K L) ≫
          (T.functorIsoTensorRight M₂).hom.app ((functor L).obj K) =
        (T.functorIsoTensorRight M₁).hom.app ((functor L).obj K) ≫
          (functor L).obj K ◁ f :=
    by
      simpa only [Monoidal.Model.objIsoTensor_hom,
        MonoidalCategory.id_tensorHom] using
        Closed.tensorMapOf_objIsoTensor H T f (obj K L)
  have hnested :
      (Closed.tensorMapOf H T g).app K ≫
          (T.functorIsoTensorRight (obj L M₂)).hom.app K =
        (T.functorIsoTensorRight (obj L M₁)).hom.app K ≫ K ◁ g :=
    by
      simpa only [Monoidal.Model.objIsoTensor_hom,
        MonoidalCategory.id_tensorHom] using
        Closed.tensorMapOf_objIsoTensor H T g K
  have hinnerInv :
      L ◁ f ≫ (T.objIsoTensor L M₂).inv =
        (T.objIsoTensor L M₁).inv ≫ g :=
    by
      simpa only [g, MonoidalCategory.id_tensorHom] using
        Closed.tensorMapOf_objIsoTensor_inv H T f L
  have hnat :
      (functor L).obj K ◁ f ≫ ((tensoringRight D).obj M₂).map
          ((T.functorIsoTensorRight L).hom.app K) =
        ((tensoringRight D).obj M₁).map
            ((T.functorIsoTensorRight L).hom.app K) ≫
          (K ⊗ L) ◁ f :=
    by
      change ((tensoringRight D).map f).app ((functor L).obj K) ≫
          ((tensoringRight D).obj M₂).map
            ((T.functorIsoTensorRight L).hom.app K) =
        ((tensoringRight D).obj M₁).map
            ((T.functorIsoTensorRight L).hom.app K) ≫
          ((tensoringRight D).map f).app ((tensorRight L).obj K)
      exact (((tensoringRight D).map f).naturality
        ((T.functorIsoTensorRight L).hom.app K)).symm
  apply (cancel_mono
    ((T.functorIsoTensorRight (obj L M₂)).hom.app K)).1
  simp only [Category.assoc]
  rw [hnested]
  conv_rhs =>
    rw [← Category.assoc, assoc_hom_objIsoTensor]
  rw [assoc_hom_objIsoTensor]
  rw [← Category.assoc, houter, Category.assoc]
  simp only [Category.assoc]
  apply (cancel_epi
    ((T.functorIsoTensorRight M₁).hom.app (obj K L))).2
  rw [← Category.assoc, hnat, Category.assoc]
  apply (cancel_epi (((tensoringRight D).obj M₁).map
    ((T.functorIsoTensorRight L).hom.app K))).2
  change (K ⊗ L) ◁ f ≫ (α_ K L M₂).hom ≫
      K ◁ (T.objIsoTensor L M₂).inv =
    (α_ K L M₁).hom ≫ K ◁ (T.objIsoTensor L M₁).inv ≫ K ◁ g
  rw [MonoidalCategory.associator_naturality_right_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp, hinnerInv]

/-- The inverse model-parametrized associator is natural in its right object for the parameter
map selected by `H` and `T`. -/
@[reassoc, stacks 0BYJ "inverse right naturality of derived tensor associativity"]
theorem assoc_inv_naturality_right
    (H : MonoidalClosed D)
    (T : Monoidal.Model (C := C))
    (K L : D) {M₁ M₂ : D} (f : M₁ ⟶ M₂) :
    (Closed.tensorMapOf H T
          ((Closed.tensorMapOf H T f).app L)).app K ≫
        (assoc T K L M₂).inv =
      (assoc T K L M₁).inv ≫
        (Closed.tensorMapOf H T f).app (obj K L) := by
  rw [Iso.comp_inv_eq (assoc T K L M₂), Category.assoc,
    Iso.eq_inv_comp (assoc T K L M₁)]
  exact (assoc_hom_naturality_right H T K L f).symm

end Closed

end CategoryTheory.DerivedCategory.DerivedTensor.Right
