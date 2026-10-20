module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map
public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Projection
public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products as a pseudofunctor on stacks

The construction first forgets the stack condition componentwise from a bundled cospan and then
applies the neutral two-fibre-product pseudofunctor on fibred categories.  The result is lifted
back to stacks using the stack-closure theorem for its object action.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.TwoFibreProduct

variable (J : GrothendieckTopology C)

/-- The ambient fibred-category-valued two-fibre-product pseudofunctor on bundled cospans of
stacks.  It is the composite of componentwise stack forgetting with the neutral
`FiberedCategoryOver.TwoFibreProduct.pseudofunctor`. -/
@[stacks 026G "ambient two-fibre-product pseudofunctor on stack cospans"]
noncomputable def ambientPseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.{u, v, max w (max u (max v vB)), max v vB} J))
      (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C) :=
  (Bicategory.Cospan.map (StackOver.forget J).toPseudofunctor).comp
    (FiberedCategoryOver.TwoFibreProduct.pseudofunctor (C := C))

/-- Every object produced by the ambient bundled-cospan construction is a stack on `J`.  This is
the sole stack-specific closure input in the lifted pseudofunctor. -/
@[stacks 026G "stack closure of ambient two-fibre products"]
theorem ambientPseudofunctor.isStackOnSite
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    IsStack.OnSite.objectProperty J ((ambientPseudofunctor J).obj S) := sorry

/-- The canonical bundled-cospan two-fibre-product pseudofunctor on stacks.  Its object,
`1`-morphism, `2`-morphism, and comparison data are inherited from the ambient construction; the
lift adds only the stack-condition witnesses. -/
@[stacks 026G "stack two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.{u, v, max w (max u (max v vB)), max v vB} J))
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J) :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (ambientPseudofunctor J) (ambientPseudofunctor.isStackOnSite J)

end StackOver.TwoFibreProduct

end CategoryTheory
