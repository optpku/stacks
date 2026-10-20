/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import StacksCheckRecall

@[expose] public section

/-!
@stack 08NM

# Source-facing bridge for Lemma 14.30.2

Mathlib's `SSet.rlp_monomorphisms` identifies lifting against boundary inclusions with lifting
against every monomorphism. The labeled source statement is the forward inclusion; the stronger
canonical equality is retained as an unlabelled companion.
-/

open CategoryTheory MorphismProperty
open SSet.modelCategoryQuillen

universe u

/- Lemma 14.30.2: a morphism lifting against every boundary inclusion lifts against every
monomorphism of simplicial sets. -/
@[stacks 08NM]
#check (le_of_eq SSet.rlp_monomorphisms.symm :
  I.rlp ≤ (monomorphisms SSet.{u}).rlp)

/- Canonical strengthening: boundary inclusions generate all monomorphisms for right lifting. -/
#check (SSet.rlp_monomorphisms :
  (monomorphisms SSet.{u}).rlp = I.rlp)
