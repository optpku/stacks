/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products as a pseudofunctor on stacks in sets

The construction forgets a bundled cospan componentwise to stacks in setoids, applies their
canonical two-fibre-product pseudofunctor, and lifts the result through the full subbicategory
selected by strict discrete fibrations.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.TwoFibreProduct

variable (J : GrothendieckTopology C)

/-- The ambient setoid-stack two-fibre-product pseudofunctor on bundled cospans of stacks in
sets. -/
@[stacks 0434 "ambient set-stack two-fibre-product pseudofunctor"]
noncomputable def ambientPseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J))
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J) :=
  (Bicategory.Cospan.map
      (StackOver.Sets.forget J).toPseudofunctor).comp
    (StackOver.Setoids.TwoFibreProduct.pseudofunctor J)

/-- Every ambient two-fibre-product object has a discrete projection. This is the sole
Sets-specific closure input to the full-subbicategory lift. -/
@[stacks 0434 "set-stack two-fibre-product closure witness"]
theorem ambientPseudofunctor.isFiberedInSets
    (S : Bicategory.Cospan
      (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    IsStack.InSets.objectProperty J ((ambientPseudofunctor J).obj S) := sorry

/-- The canonical bundled-cospan two-fibre-product pseudofunctor on stacks in sets. -/
@[stacks 0434 "set-stack two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J))
      (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J) :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (ambientPseudofunctor J) (ambientPseudofunctor.isFiberedInSets J)

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
