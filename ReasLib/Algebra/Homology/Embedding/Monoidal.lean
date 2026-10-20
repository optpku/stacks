/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal extension of homological complexes

An additive embedding of complex shapes transports the degree-zero object and the degree sums
which define tensor products of homological complexes.  Compatibility with the tensor signs then
makes extension by zero a strong monoidal functor.  This file exposes both directions of the unit
and tensor comparisons before packaging their coherence in a monoidal functor structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe w w' v u

namespace ComplexShape.Embedding

section Shape

variable {I : Type w} {I' : Type w'} [AddMonoid I] [AddMonoid I']
variable {c : ComplexShape I} {c' : ComplexShape I'}

/-- An embedding of complex shapes is additive when its map on degrees preserves zero and sums. -/
@[stacks 0FP8 "additive embedding of complex shapes"]
class IsAdditive (e : c.Embedding c') : Prop where
  /-- The distinguished degree zero is preserved. -/
  zero : e.f 0 = 0
  /-- Sums of degrees are preserved. -/
  add (i j : I) : e.f (i + j) = e.f i + e.f j

/-- The additive homomorphism on degrees underlying an additive embedding of complex shapes. -/
@[stacks 0FP8 "additive homomorphism underlying an embedding of complex shapes"]
def addMonoidHom (e : c.Embedding c') [e.IsAdditive] : I →+ I' where
  toFun := e.f
  map_zero' := IsAdditive.zero
  map_add' := IsAdditive.add

/-- An additive embedding preserves degree zero. -/
@[simp]
lemma map_zero (e : c.Embedding c') [e.IsAdditive] : e.f 0 = 0 := sorry

/-- An additive embedding preserves sums of degrees. -/
@[simp]
lemma map_add (e : c.Embedding c') [e.IsAdditive] (i j : I) :
    e.f (i + j) = e.f i + e.f j := sorry

/-- Additivity identifies a sum after recovering both summands through the partial inverse. -/
lemma map_add_eq_of_r_eq_some (e : c.Embedding c') [e.IsAdditive]
    {i' j' : I'} {i j : I} (hi : e.r i' = some i) (hj : e.r j' = some j) :
    e.f (i + j) = i' + j' := sorry

/-- An additive embedding preserves tensor signs when it also preserves the sign assigned to each
degree. -/
@[stacks 0FP8 "embedding preserving tensor signs"]
class PreservesTensorSigns (e : c.Embedding c') [c.TensorSigns] [c'.TensorSigns] :
    Prop extends e.IsAdditive where
  /-- The sign of every degree is preserved. -/
  epsilon (i : I) : c'.ε (e.f i) = c.ε i

/-- An embedding preserving tensor signs preserves the sign of every degree. -/
@[simp]
lemma map_epsilon (e : c.Embedding c') [c.TensorSigns] [c'.TensorSigns]
    [e.PreservesTensorSigns] (i : I) : c'.ε (e.f i) = c.ε i := sorry

end Shape

section Comparisons

variable {I : Type w} {I' : Type w'} [AddMonoid I] [AddMonoid I']
variable {c : ComplexShape I} {c' : ComplexShape I'}
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
variable [HasZeroObject C] [MonoidalPreadditive C]
variable [DecidableEq I] [DecidableEq I'] [c.TensorSigns] [c'.TensorSigns]
variable (e : c.Embedding c')

/-- The tensor unit in the target shape is canonically the extension of the tensor unit in the
source shape. -/
@[stacks 0FP8 "unit comparison for extension of homological complexes"]
noncomputable def extendUnitIso [e.IsAdditive] :
    HomologicalComplex.tensorUnit C c' ≅
      (HomologicalComplex.tensorUnit C c).extend e :=
  (HomologicalComplex.extendSingleIso e (𝟙_ C) 0 0 e.addMonoidHom.map_zero).symm

/-- At degree zero, the forward unit comparison is the canonical map from the target single
complex to the extended source single complex. -/
@[reassoc]
theorem extendUnitIso_hom_f [e.IsAdditive] :
    (e.extendUnitIso (C := C)).hom.f 0 =
      (HomologicalComplex.singleObjXSelf c' 0 (𝟙_ C)).hom ≫
        (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).inv ≫
          ((HomologicalComplex.tensorUnit C c).extendXIso e
            e.addMonoidHom.map_zero).inv := sorry

/-- At degree zero, the inverse unit comparison is the canonical map from the extended source
single complex to the target single complex. -/
@[reassoc]
theorem extendUnitIso_inv_f [e.IsAdditive] :
    (e.extendUnitIso (C := C)).inv.f 0 =
      ((HomologicalComplex.tensorUnit C c).extendXIso e
          e.addMonoidHom.map_zero).hom ≫
        (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C)).hom ≫
          (HomologicalComplex.singleObjXSelf c' 0 (𝟙_ C)).inv := sorry

variable (K L : HomologicalComplex C c)
variable [HomologicalComplex.HasTensor K L]
variable [HomologicalComplex.HasTensor (K.extend e) (L.extend e)]

/-- The degreewise data of the forward tensor comparison for extension by zero. -/
@[stacks 0FP8 "degreewise forward tensor comparison for extension of homological complexes"]
noncomputable def extendTensorHomF [e.IsAdditive] (n' : I') :
    (HomologicalComplex.tensorObj (K.extend e) (L.extend e)).X n' ⟶
      ((HomologicalComplex.tensorObj K L).extend e).X n' :=
  HomologicalComplex.mapBifunctorDesc fun i' j' hij ↦
    match hi : e.r i', hj : e.r j' with
    | some i, some j =>
        ((K.extendXIso e (e.f_eq_of_r_eq_some hi)).hom ⊗ₘ
            (L.extendXIso e (e.f_eq_of_r_eq_some hj)).hom) ≫
          HomologicalComplex.ιTensorObj K L i j (i + j) rfl ≫
            ((HomologicalComplex.tensorObj K L).extendXIso e
              ((e.addMonoidHom.map_add i j).trans
                ((congrArg₂ (· + ·) (e.f_eq_of_r_eq_some hi)
                  (e.f_eq_of_r_eq_some hj)).trans hij))).inv
    | _, _ => 0

/-- The degreewise forward tensor comparison commutes with the differentials. -/
theorem extendTensorHomF_comm [e.PreservesTensorSigns]
    (i' j' : I') (hij : c'.Rel i' j') :
    e.extendTensorHomF K L i' ≫
        ((HomologicalComplex.tensorObj K L).extend e).d i' j' =
      (HomologicalComplex.tensorObj (K.extend e) (L.extend e)).d i' j' ≫
        e.extendTensorHomF K L j' := sorry

/-- The forward tensor comparison for extension by zero, defined on every homogeneous summand. -/
@[stacks 0FP8 "forward tensor comparison for extension of homological complexes"]
noncomputable def extendTensorHom [e.PreservesTensorSigns] :
    HomologicalComplex.tensorObj (K.extend e) (L.extend e) ⟶
      (HomologicalComplex.tensorObj K L).extend e where
  f := e.extendTensorHomF K L
  comm' := e.extendTensorHomF_comm K L

/-- The degreewise data of the inverse tensor comparison for extension by zero. -/
@[stacks 0FP8 "degreewise inverse tensor comparison for extension of homological complexes"]
noncomputable def extendTensorInvF [e.IsAdditive] (n' : I') :
    ((HomologicalComplex.tensorObj K L).extend e).X n' ⟶
      (HomologicalComplex.tensorObj (K.extend e) (L.extend e)).X n' :=
  match hn : e.r n' with
  | none => 0
  | some _ =>
      ((HomologicalComplex.tensorObj K L).extendXIso e
          (e.f_eq_of_r_eq_some hn)).hom ≫
        HomologicalComplex.mapBifunctorDesc fun i j hij ↦
          ((K.extendXIso e rfl).inv ⊗ₘ (L.extendXIso e rfl).inv) ≫
            HomologicalComplex.ιTensorObj (K.extend e) (L.extend e)
              (e.f i) (e.f j) n'
              ((e.addMonoidHom.map_add i j).symm.trans
                ((congrArg e.f hij).trans (e.f_eq_of_r_eq_some hn)))

/-- The degreewise inverse tensor comparison commutes with the differentials. -/
theorem extendTensorInvF_comm [e.PreservesTensorSigns]
    (i' j' : I') (hij : c'.Rel i' j') :
    e.extendTensorInvF K L i' ≫
        (HomologicalComplex.tensorObj (K.extend e) (L.extend e)).d i' j' =
      ((HomologicalComplex.tensorObj K L).extend e).d i' j' ≫
        e.extendTensorInvF K L j' := sorry

/-- The inverse tensor comparison for extension by zero, obtained degreewise from the recovered
source degree. -/
@[stacks 0FP8 "inverse tensor comparison for extension of homological complexes"]
noncomputable def extendTensorInv [e.PreservesTensorSigns] :
    (HomologicalComplex.tensorObj K L).extend e ⟶
      HomologicalComplex.tensorObj (K.extend e) (L.extend e) where
  f := e.extendTensorInvF K L
  comm' := e.extendTensorInvF_comm K L

/-- On an image summand, the forward tensor comparison is the tensor of the component
identifications followed by the corresponding coproduct inclusion. -/
@[reassoc (attr := simp)]
theorem ι_extendTensorHom [e.PreservesTensorSigns] (i j : I) :
    HomologicalComplex.ιTensorObj (K.extend e) (L.extend e)
        (e.f i) (e.f j) (e.f (i + j)) (e.map_add i j).symm ≫
      (e.extendTensorHom K L).f (e.f (i + j)) =
        ((K.extendXIso e rfl).hom ⊗ₘ (L.extendXIso e rfl).hom) ≫
          HomologicalComplex.ιTensorObj K L i j (i + j) rfl ≫
            ((HomologicalComplex.tensorObj K L).extendXIso e rfl).inv := sorry

/-- On an image summand, the inverse tensor comparison recovers the tensor of the component
identifications. -/
@[reassoc (attr := simp)]
theorem ι_extendTensorInv [e.PreservesTensorSigns] (i j : I) :
    HomologicalComplex.ιTensorObj K L i j (i + j) rfl ≫
        ((HomologicalComplex.tensorObj K L).extendXIso e rfl).inv ≫
          (e.extendTensorInv K L).f (e.f (i + j)) =
      ((K.extendXIso e rfl).inv ⊗ₘ (L.extendXIso e rfl).inv) ≫
        HomologicalComplex.ιTensorObj (K.extend e) (L.extend e)
          (e.f i) (e.f j) (e.f (i + j)) (e.map_add i j).symm := sorry

/-- The forward and inverse tensor comparisons compose to the identity on the tensor product of
extended complexes. -/
theorem extendTensorHom_comp_extendTensorInv [e.PreservesTensorSigns] :
    e.extendTensorHom K L ≫ e.extendTensorInv K L = 𝟙 _ := sorry

/-- The inverse and forward tensor comparisons compose to the identity on the extension of the
source tensor product. -/
theorem extendTensorInv_comp_extendTensorHom [e.PreservesTensorSigns] :
    e.extendTensorInv K L ≫ e.extendTensorHom K L = 𝟙 _ := sorry

/-- Extension by zero preserves tensor products along an embedding preserving tensor signs. -/
@[stacks 0FP8 "tensor comparison isomorphism for extension of homological complexes"]
noncomputable def extendTensorIso [e.PreservesTensorSigns] :
    HomologicalComplex.tensorObj (K.extend e) (L.extend e) ≅
      (HomologicalComplex.tensorObj K L).extend e where
  hom := e.extendTensorHom K L
  inv := e.extendTensorInv K L
  hom_inv_id := e.extendTensorHom_comp_extendTensorInv K L
  inv_hom_id := e.extendTensorInv_comp_extendTensorHom K L

/-- The forward map of the tensor comparison is the explicit forward comparison morphism. -/
@[simp]
theorem extendTensorIso_hom [e.PreservesTensorSigns] :
    (e.extendTensorIso K L).hom = e.extendTensorHom K L := sorry

/-- The inverse map of the tensor comparison is the explicit inverse comparison morphism. -/
@[simp]
theorem extendTensorIso_inv [e.PreservesTensorSigns] :
    (e.extendTensorIso K L).inv = e.extendTensorInv K L := sorry

end Comparisons

section Monoidal

variable {I : Type w} {I' : Type w'} [AddMonoid I] [AddMonoid I']
variable {c : ComplexShape I} {c' : ComplexShape I'}
variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
variable [HasZeroObject C] [MonoidalPreadditive C]
variable [DecidableEq I] [DecidableEq I'] [c.TensorSigns] [c'.TensorSigns]
variable [∀ X Y : GradedObject I C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject I C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject I C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ W X Y Z : GradedObject I C, GradedObject.HasTensor₄ObjExt W X Y Z]
variable [∀ X Y : GradedObject I' C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject I' C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject I' C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ W X Y Z : GradedObject I' C, GradedObject.HasTensor₄ObjExt W X Y Z]
variable (e : c.Embedding c') [e.PreservesTensorSigns]

/-- The tensor comparison for extension by zero is natural in its left argument. -/
theorem extendTensorIso_natural_left {K L : HomologicalComplex C c} (f : K ⟶ L)
    (M : HomologicalComplex C c) :
    (e.extendFunctor C).map f ▷ (e.extendFunctor C).obj M ≫
        (e.extendTensorIso L M).hom =
      (e.extendTensorIso K M).hom ≫ (e.extendFunctor C).map (f ▷ M) := sorry

/-- The tensor comparison for extension by zero is natural in its right argument. -/
theorem extendTensorIso_natural_right (K : HomologicalComplex C c)
    {L M : HomologicalComplex C c} (f : L ⟶ M) :
    (e.extendFunctor C).obj K ◁ (e.extendFunctor C).map f ≫
        (e.extendTensorIso K M).hom =
      (e.extendTensorIso K L).hom ≫ (e.extendFunctor C).map (K ◁ f) := sorry

/-- The tensor comparison for extension by zero respects associators. -/
theorem extendTensorIso_associativity (K L M : HomologicalComplex C c) :
    (e.extendTensorIso K L).hom ▷ (e.extendFunctor C).obj M ≫
        (e.extendTensorIso (K ⊗ L) M).hom ≫
          (e.extendFunctor C).map (α_ K L M).hom =
      (α_ ((e.extendFunctor C).obj K) ((e.extendFunctor C).obj L)
          ((e.extendFunctor C).obj M)).hom ≫
        (e.extendFunctor C).obj K ◁ (e.extendTensorIso L M).hom ≫
          (e.extendTensorIso K (L ⊗ M)).hom := sorry

/-- The unit and tensor comparisons for extension by zero respect the left unitor. -/
theorem extendTensorIso_left_unitality (K : HomologicalComplex C c) :
    (λ_ ((e.extendFunctor C).obj K)).hom =
      (e.extendUnitIso (C := C)).hom ▷ (e.extendFunctor C).obj K ≫
        (e.extendTensorIso (𝟙_ (HomologicalComplex C c)) K).hom ≫
          (e.extendFunctor C).map (λ_ K).hom := sorry

/-- The unit and tensor comparisons for extension by zero respect the right unitor. -/
theorem extendTensorIso_right_unitality (K : HomologicalComplex C c) :
    (ρ_ ((e.extendFunctor C).obj K)).hom =
      (e.extendFunctor C).obj K ◁ (e.extendUnitIso (C := C)).hom ≫
        (e.extendTensorIso K (𝟙_ (HomologicalComplex C c))).hom ≫
          (e.extendFunctor C).map (ρ_ K).hom := sorry

/-- The canonical coherence data making extension by zero a strong monoidal functor. -/
@[stacks 0FP8 "monoidal core for extension of homological complexes"]
noncomputable def extendCoreMonoidal : (e.extendFunctor C).CoreMonoidal where
  εIso := e.extendUnitIso
  μIso := fun K L ↦ e.extendTensorIso K L
  μIso_hom_natural_left := e.extendTensorIso_natural_left (C := C)
  μIso_hom_natural_right := fun K f ↦
    e.extendTensorIso_natural_right (C := C) K f
  associativity := e.extendTensorIso_associativity (C := C)
  left_unitality := e.extendTensorIso_left_unitality (C := C)
  right_unitality := e.extendTensorIso_right_unitality (C := C)

/-- Extension by zero along an embedding preserving tensor signs is a strong monoidal functor. -/
@[stacks 0FP8 "extension of homological complexes is monoidal", implicit_reducible]
noncomputable instance extendFunctorMonoidal : (e.extendFunctor C).Monoidal :=
  e.extendCoreMonoidal.toMonoidal

end Monoidal

end ComplexShape.Embedding


-- The comparison morphisms are explicit; `sorryAx` is confined to their chain-map,
-- inverse, naturality, and coherence laws.
