/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Order.Directed.Characterization
public import ReasLib.Algebra.Category.CommRingCat.DirectedSystem
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory

section

variable (I : Type u) [Preorder I]

/- Definition 111.2.1 (1): a directed set is a nonempty preordered type in which every pair of
elements has a common upper bound. -/
@[stacks 078I]
#check (Order.nonempty_isDirectedOrder_iff I :
  (Nonempty I ∧ IsDirectedOrder I) ↔
    (Nonempty I ∧ ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k))

end

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/- Definition 111.2.1 (2): a system of rings over a directed set `I` consists of rings
`rings i` and transition morphisms for `i ≤ j`, subject only to composition compatibility.
Self-transitions need not be identities. Functors `I ⥤ CommRingCat` form an
identity-preserving special case, as expressed by `CommRingCat.isCompatibleSystem_of_functor`. -/
@[stacks 078I]
#check (CommRingCat.IsCompatibleSystem (I := I) :
  (rings : I → CommRingCat.{v}) →
    (∀ {i j : I}, i ≤ j → (rings i ⟶ rings j)) → Prop)

end
