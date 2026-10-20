/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products as a pseudofunctor on groupoid stacks

The construction first forgets the stack condition componentwise from a bundled cospan, then
applies the neutral `CategoryTheory.TwoFibreProduct.pseudofunctor`.  The result is lifted back to
the full subbicategory of stacks using only the stack-closure theorem for its object action.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids.TwoFibreProduct

variable (J : GrothendieckTopology C)

/-- The ambient groupoid-fibred two-fibre-product pseudofunctor on bundled cospans of stacks.

It is the composite of componentwise stack forgetting with the neutral explicit
two-fibre-product pseudofunctor. -/
@[stacks 02ZL "ambient groupoid-stack two-fibre-product pseudofunctor"]
noncomputable def ambientPseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J))
      (FiberedCategoryOver.Groupoids.{u, v,
        max w (max u (max v vB)), max v vB} C) :=
  (Bicategory.Cospan.map
      (StackOver.Groupoids.forget J).toPseudofunctor).comp
    (CategoryTheory.TwoFibreProduct.pseudofunctor
      (BasedCategory.isFiberedInGroupoids C))

/-- Every object produced by the ambient bundled-cospan construction is a stack on the site.
This is the sole stack-specific closure input in the lifted pseudofunctor. -/
@[stacks 02ZL "stack closure for groupoid-stack two-fibre products"]
theorem ambientPseudofunctor.isStackOnSite
    (S : Bicategory.Cospan
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    IsStack.InGroupoids.objectProperty J ((ambientPseudofunctor J).obj S) := sorry

/-- The canonical bundled-cospan two-fibre-product pseudofunctor on stacks in groupoids.

All object, `1`-cell, `2`-cell, and comparison data are inherited from the neutral
`CategoryTheory.TwoFibreProduct.pseudofunctor`; the lift adds only stack-membership proofs. -/
@[stacks 02ZL "groupoid-stack two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J))
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J) :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (ambientPseudofunctor J) (ambientPseudofunctor.isStackOnSite J)

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
