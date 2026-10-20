/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.At.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# The hom category of bicategorical cospan transformations

Strong transformations between two canonical walking-cospan diagrams form a category whose
morphisms are modifications. This file gives that canonical category structure a
cospan-specific scope.

The instance is deliberately scoped: the ambient pseudofunctor API also supports lax and oplax
transformations, so installing one transformation category globally would make instance search
choose a presentation that is not canonical outside the cospan API. Downstream files can enable
this instance with
`open scoped CategoryTheory.Bicategory.CospanTransform`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The canonical category of strong transformations between two walking-cospan diagrams,
with modifications as morphisms. -/
scoped instance homCategory :
    Category (CospanTransform f g f' g') :=
  Pseudofunctor.StrongTrans.homCategory

open scoped CategoryTheory.Bicategory.CospanTransform

/-- Evaluation of cospan transformations and modifications at the left endpoint. -/
@[stacks 0040 "left-endpoint functor on cospan transformations"]
def leftFunctor :
    CospanTransform f g f' g' ⥤ (x ⟶ x') :=
  Pseudofunctor.evaluationHom
    (LocallyDiscrete.mk Limits.WalkingCospan.left) (cospan f g) (cospan f' g')

/-- The object action of `leftFunctor` is the left component of a cospan transformation. -/
@[simp]
theorem leftFunctor.obj (ψ : CospanTransform f g f' g') :
    leftFunctor.obj ψ = ψ.left := sorry

/-- The morphism action of `leftFunctor` is the left component of a cospan modification. -/
@[simp]
theorem leftFunctor.map_apply
    {ψ φ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    leftFunctor.map Γ = Hom.left Γ := sorry

/-- Evaluation of cospan transformations and modifications at the right endpoint. -/
@[stacks 0040 "right-endpoint functor on cospan transformations"]
def rightFunctor :
    CospanTransform f g f' g' ⥤ (y ⟶ y') :=
  Pseudofunctor.evaluationHom
    (LocallyDiscrete.mk Limits.WalkingCospan.right) (cospan f g) (cospan f' g')

/-- The object action of `rightFunctor` is the right component of a cospan transformation. -/
@[simp]
theorem rightFunctor.obj (ψ : CospanTransform f g f' g') :
    rightFunctor.obj ψ = ψ.right := sorry

/-- The morphism action of `rightFunctor` is the right component of a cospan modification. -/
@[simp]
theorem rightFunctor.map_apply
    {ψ φ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    rightFunctor.map Γ = Hom.right Γ := sorry

/-- Evaluation of cospan transformations and modifications at the common target. -/
@[stacks 0040 "base functor on cospan transformations"]
def baseFunctor :
    CospanTransform f g f' g' ⥤ (z ⟶ z') :=
  Pseudofunctor.evaluationHom
    (LocallyDiscrete.mk Limits.WalkingCospan.one) (cospan f g) (cospan f' g')

/-- The object action of `baseFunctor` is the common-target component of a cospan
transformation. -/
@[simp]
theorem baseFunctor.obj (ψ : CospanTransform f g f' g') :
    baseFunctor.obj ψ = ψ.base := sorry

/-- The morphism action of `baseFunctor` is the common-target component of a cospan
modification. -/
@[simp]
theorem baseFunctor.map_apply
    {ψ φ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    baseFunctor.map Γ = Hom.base Γ := sorry

/- Data and axiom audit (mathlib 4.32):

The instance is definitionally the existing strong-transformation hom category, so its objects,
morphisms, identities, and compositions introduce no new data. `#print axioms` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; `sorryAx` is inherited from the
Prop-valued modification and category laws. -/

end CategoryTheory.Bicategory.CospanTransform
