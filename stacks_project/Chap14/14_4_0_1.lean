/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 016H
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (U U' : SimplicialObject C)

/- 14.4.0.1: morphisms of simplicial objects are natural transformations. -/
@[stacks 016H]
#check (rfl : (U ⟶ U') = NatTrans U U')

/- The two sides remain available independently as a typed companion check. -/
#check (NatTrans U U' : Type v)
#check (U ⟶ U' : Type v)
