/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Tensor descent for regraded objects

`GradedObject.mapObj` collects the homogeneous pieces in one fibre of an index map by a
coproduct. When tensoring preserves the relevant coproducts, maps on pairs of original
homogeneous pieces descend canonically to the tensor of two regraded components. This is the
generic four-degree coproduct step used by total-complex tensor comparisons.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe wI wJ wP wQ v u
universe uA vA uB vB uD vD

namespace CategoryTheory.GradedObject

section Bifunctor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {D : Type uD} [Category.{vD} D]
variable {T : A ⥤ B ⥤ D}
variable {I' : Type wI} {J' : Type wJ} {P' : Type wP} {Q' : Type wQ}
variable (X' : GradedObject I' A) (Y' : GradedObject J' B)
variable (p' : I' → P') (q' : J' → Q') [X'.HasMap p'] [Y'.HasMap q']
variable [HasCoproducts.{wI} A] [HasCoproducts.{wJ} B]
variable [HasCoproducts.{wI} D] [HasCoproducts.{wJ} D]
variable [∀ Z : A, PreservesColimitsOfSize.{wJ, wJ} (T.obj Z)]
variable [∀ Z : B, PreservesColimitsOfSize.{wI, wI} (T.flip.obj Z)]

/-- Descend maps on pairs of homogeneous pieces for a curried bifunctor. -/
@[stacks 07MB "bifunctor descent for regraded coproduct components"]
noncomputable def mapObjBifunctorDesc (a : P') (b : Q') {Z : D}
    (f : ∀ i (_ : p' i = a) j (_ : q' j = b),
      (T.obj (X' i)).obj (Y' j) ⟶ Z) :
    (T.obj (X'.mapObj p' a)).obj (Y'.mapObj q' b) ⟶ Z :=
  (PreservesCoproduct.iso (T.obj (X'.mapObj p' a)) (Y'.mapObjFun q' b)).hom ≫
    Limits.Sigma.map (fun j : q' ⁻¹' {b} ↦
      (PreservesCoproduct.iso (T.flip.obj (Y' j.1)) (X'.mapObjFun p' a)).hom) ≫
    Limits.Sigma.desc (fun j : q' ⁻¹' {b} ↦
      Limits.Sigma.desc (fun i : p' ⁻¹' {a} ↦ f i.1 i.2 j.1 j.2))

/-- A regraded bifunctor descent restricts to its supplied homogeneous component. -/
@[reassoc, stacks 07MB "homogeneous component of regraded bifunctor descent"]
theorem ιMapObj_mapObjBifunctorDesc (a : P') (b : Q') {Z : D}
    (f : ∀ i (_ : p' i = a) j (_ : q' j = b),
      (T.obj (X' i)).obj (Y' j) ⟶ Z)
    (i : I') (hi : p' i = a) (j : J') (hj : q' j = b) :
    (T.map (X'.ιMapObj p' i a hi)).app (Y' j) ≫
        (T.obj (X'.mapObj p' a)).map (Y'.ιMapObj q' j b hj) ≫
      mapObjBifunctorDesc X' Y' p' q' (T := T) a b f = f i hi j hj := sorry

end Bifunctor

variable {I : Type wI} {J : Type wJ} {P : Type wP} {Q : Type wQ}
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X : GradedObject I C) (Y : GradedObject J C)
variable (p : I → P) (q : J → Q) [X.HasMap p] [Y.HasMap q]
variable [HasCoproducts.{wI} C] [HasCoproducts.{wJ} C]
variable [∀ Z : C, PreservesColimitsOfSize.{wI, wI} ((curriedTensor C).flip.obj Z)]
variable [∀ Z : C, PreservesColimitsOfSize.{wJ, wJ} ((curriedTensor C).obj Z)]

/-- Descend maps on pairs of homogeneous pieces to the tensor of two regraded components. -/
@[stacks 07MB "tensor descent for regraded coproduct components"]
noncomputable def mapObjTensorDesc (a : P) (b : Q) {Z : C}
    (f : ∀ i (_ : p i = a) j (_ : q j = b), X i ⊗ Y j ⟶ Z) :
    X.mapObj p a ⊗ Y.mapObj q b ⟶ Z :=
  (PreservesCoproduct.iso ((curriedTensor C).flip.obj (Y.mapObj q b))
      (X.mapObjFun p a)).hom ≫
    Limits.Sigma.map (fun i : p ⁻¹' {a} ↦
      (PreservesCoproduct.iso ((curriedTensor C).obj (X i.1))
        (Y.mapObjFun q b)).hom) ≫
    Limits.Sigma.desc (fun i : p ⁻¹' {a} ↦
      Limits.Sigma.desc (fun j : q ⁻¹' {b} ↦ f i.1 i.2 j.1 j.2))

/-- On two homogeneous summands, `mapObjTensorDesc` is the supplied component map. -/
@[reassoc, stacks 07MB "homogeneous component of regraded tensor descent"]
theorem ιMapObj_tensor_mapObjTensorDesc (a : P) (b : Q) {Z : C}
    (f : ∀ i (_ : p i = a) j (_ : q j = b), X i ⊗ Y j ⟶ Z)
    (i : I) (hi : p i = a) (j : J) (hj : q j = b) :
    (X.ιMapObj p i a hi ⊗ₘ Y.ιMapObj q j b hj) ≫
      mapObjTensorDesc X Y p q a b f = f i hi j hj := sorry

end CategoryTheory.GradedObject

end
