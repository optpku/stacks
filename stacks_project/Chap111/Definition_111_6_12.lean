/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Topology.Sober.GenericPoint

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]

/- Definition 111.6.12: a point `x` of an irreducible topological space `X` is a generic
point of `X` when `Set.univ = closure {x}`. -/
@[stacks 027E] #check (isGenericPoint_univ_iff_eq_closure (X := X) :
  ∀ x : X, IsGenericPoint x Set.univ ↔ (Set.univ : Set X) = closure ({x} : Set X))
