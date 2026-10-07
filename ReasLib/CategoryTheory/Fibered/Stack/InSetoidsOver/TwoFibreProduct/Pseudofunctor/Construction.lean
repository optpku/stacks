module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute
/-!
# Two-fibre products as a pseudofunctor on stacks in setoids

The construction forgets a bundled cospan of setoid stacks componentwise to groupoid stacks,
applies the existing groupoid-stack two-fibre-product pseudofunctor, and lifts the result through
the full subbicategory selected by the thin-fibre condition. Thus all action and coherence data
ultimately come from the neutral locally induced two-fibre-product pseudofunctor.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids.TwoFibreProduct

variable (J : GrothendieckTopology C)

/-- The ambient groupoid-stack two-fibre-product pseudofunctor on bundled cospans of setoid
stacks. It is obtained by componentwise forgetting followed by the canonical groupoid-stack
construction. -/
@[stacks 0434 "ambient setoid-stack two-fibre-product pseudofunctor"]
noncomputable def ambientPseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J))
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J) :=
  (Bicategory.Cospan.map
      (StackOver.Setoids.forget J).toPseudofunctor).comp
    (StackOver.Groupoids.TwoFibreProduct.pseudofunctor J)

/-- Every object produced by the ambient construction has thin fibers. This is the sole
setoid-specific closure input used by the lifted pseudofunctor. -/
@[stacks 0434 "setoid-stack two-fibre-product closure witness"]
theorem ambientPseudofunctor.isFiberedInSetoids
    (S : Bicategory.Cospan
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    IsStack.InSetoids.objectProperty J ((ambientPseudofunctor J).obj S) := sorry

/-- The canonical bundled-cospan two-fibre-product pseudofunctor on stacks in setoids. Its
non-`Prop` data are inherited from the neutral construction; the lift adds only the thin-fibre
membership proof. -/
@[stacks 0434 "setoid-stack two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J))
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J) :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (ambientPseudofunctor J) (ambientPseudofunctor.isFiberedInSetoids J)

end StackOver.Setoids.TwoFibreProduct

end CategoryTheory
