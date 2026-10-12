/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Sets.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete sources in two-fibre products of groupoid stacks

This leaf isolates the set-valued closure of the neutral groupoid-stack two-fibre product.  The
sources need only have discrete projections; the common target remains an arbitrary stack in
groupoids.  The underlying closure is supplied by the explicit based pseudo-pullback API.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.TwoFibreProduct

variable {X Y Z :
  StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J}

/-- The two-fibre product of groupoid stacks with discrete source projections again has a
discrete projection.  No discreteness assumption is required on the common target. -/
@[stacks 0047 "discrete closure of a groupoid-stack two-fibre product"]
instance isDiscreteFibration
    (F : X ⟶ Z) (G : Y ⟶ Z)
    [Functor.IsDiscreteFibration X.p] [Functor.IsDiscreteFibration Y.p] :
    Functor.IsDiscreteFibration (apex F G).p := sorry

section

variable (F : X ⟶ Z) (G : Y ⟶ Z)
variable [Functor.IsDiscreteFibration X.p] [Functor.IsDiscreteFibration Y.p]

#synth Functor.IsDiscreteFibration (apex F G).p
#synth IsStack.InSets J (apex F G).p

end

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
