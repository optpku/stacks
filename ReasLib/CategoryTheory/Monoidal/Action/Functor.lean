/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Multifunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor actions induced by functors

A functor `F : C ⥤ D` into a monoidal category lets objects of `C` act on the right of objects
of `D`: the mixed tensor of `X : D` and `Y : C` is `X ⊗ F.obj Y`.  This file exposes the
uncurried bifunctor and its functoriality in `F`; monoidal coherence can be added independently
when `F` is strong monoidal.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

universe uC vC uD vD

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

/-- The right tensor action induced by `F : C ⥤ D`, as an uncurried bifunctor
`D × C ⥤ D`. -/
@[stacks 08I6 "tensor action along a functor"]
def tensorRightAction (F : C ⥤ D) : D × C ⥤ D :=
  Functor.prod (𝟭 D) F ⋙ tensor D

/-- The mixed tensor object for the right tensor action induced by `F`. -/
@[stacks 08I6 "mixed tensor along a functor"]
abbrev tensorRightActionObj (F : C ⥤ D) (X : D) (Y : C) : D :=
  (tensorRightAction F).obj (X, Y)

namespace TensorRightAction

/-- Scoped notation for the mixed tensor `X ⊗ F.obj Y` induced by `F : C ⥤ D`. -/
scoped notation:70 X:70 " ⊗[" F "] " Y:71 => tensorRightActionObj F X Y

end TensorRightAction

/-- A natural transformation of coefficient functors induces a natural transformation of their
right tensor actions. -/
def tensorRightActionMap {F G : C ⥤ D} (α : F ⟶ G) :
    tensorRightAction F ⟶ tensorRightAction G :=
  Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 D)) α) (tensor D)

/-- A natural isomorphism of coefficient functors induces a natural isomorphism of their right
tensor actions. -/
def tensorRightActionIso {F G : C ⥤ D} (e : F ≅ G) :
    tensorRightAction F ≅ tensorRightAction G :=
  Functor.isoWhiskerRight (NatIso.prod (Iso.refl (𝟭 D)) e) (tensor D)

/-- The mixed tensor induced by `F` is definitionally the ambient tensor with `F.obj Y`. -/
@[simp]
theorem tensorRightActionObj_eq (F : C ⥤ D) (X : D) (Y : C) :
    tensorRightActionObj F X Y = X ⊗ F.obj Y := sorry

end CategoryTheory.Functor
