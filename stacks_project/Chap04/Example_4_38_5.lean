/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- Import decisions:
-- * `DiscreteFibration.Elements` is public because the projection clause uses the named
--   category-of-elements discrete-fibration instance and its exported canonical owners.
-- * `DiscreteFibration.Fibers` is public because the final clause uses the generic theorem
--   that standard fibers of any discrete fibration are discrete.
-- * `StacksCheckRecall` remains plain because it is needed only for source annotations.
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Elements
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]
variable (F : Cᵒᵖ ⥤ Type w)
variable (x y : F.Elements) (f : x.1 ⟶ y.1)
variable (hf : F.map f x.2 = y.2) (U : C)

/-
For a presheaf `F : Cᵒᵖ ⥤ Type w`, mathlib's covariant category of elements is formed over
`Cᵒᵖ`; taking opposites gives the source's contravariant category of elements over `C`.
Thus the semantic owners are already `F.Elementsᵒᵖ` and `(π F).leftOp`, not a new hand-written
category or a specialization of the heavier Cat-valued Grothendieck construction.

The canonical expressions are already shorter than any source-facing wrapper, so clients use
`F.Elementsᵒᵖ` and `(π F).leftOp` directly. No extra abbreviation or notation is introduced.
-/

/- Example 4.38.5 (objects): `Functor.Elements` owns the pairs `(U, x)`; after taking
opposites these are precisely `U : C` together with `x : F.obj (op U)`. -/
@[stacks 04TM "objects as base-element pairs"]
#check (Functor.Elements F : Type max u w)

/- Example 4.38.5 (morphisms): `CategoryOfElements.homMk`, applied before taking opposites,
owns a base arrow together with the equation asserting that it transports one element to the
other. -/
@[stacks 04TM "morphisms as base arrows satisfying the restriction equation"]
#check (CategoryOfElements.homMk x y f hf : x ⟶ y)

/- Example 4.38.5 (composition): the canonical category instance inherits composition from the
base and uses functoriality of `F` for the element equation. -/
@[stacks 04TM "identity and composition in the category of elements"]
#check (CategoryTheory.categoryOfElements F : Category.{v} F.Elements)

/- Example 4.38.5 (projection): `CategoryOfElements.π` forgets the element; its left opposite is
the source projection `p_F : 𝒮_F ⥤ C`. -/
@[stacks 04TM "projection to the base category"]
#check (CategoryOfElements.π F : F.Elements ⥤ Cᵒᵖ)

/- Example 4.38.5 (discrete fibration): the contravariant category-of-elements projection has a
unique lift of every base morphism with prescribed codomain. -/
@[stacks 04TM "the projection is a discrete fibration"]
#check (CategoryOfElements.π.leftOp.isDiscreteFibration F :
  Functor.IsDiscreteFibration ((CategoryOfElements.π F).leftOp))

namespace CategoryOfElements

/- Example 4.38.5 (fibres): the standard fibre of the projection is discrete. Its objects carry
an element of `F.obj (op U)` together with the equality witness imposed by `Functor.Fiber`; thus
the textbook's underlying-set identification is canonical up to that equality transport, not a
second carrier that should be introduced as public data. -/
@[stacks 04TM "the standard fibres are discrete"]
#check (Functor.IsDiscreteFibration.fiberIsDiscrete
    ((CategoryOfElements.π F).leftOp) U :
  IsDiscrete (((CategoryOfElements.π F).leftOp).Fiber U))

end CategoryOfElements

end CategoryTheory
