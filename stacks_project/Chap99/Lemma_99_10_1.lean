/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.OpenImmersion

/-!
# The Picard stack is open in the stack of coherent sheaves

For a flat, finitely presented, proper morphism of algebraic spaces, the
natural inclusion `Picard.toCoh f` is representable by open immersions.
The pinned source identifies this with the following equivalent criterion:
each coherent family has an open subscheme representing all base changes
on which its actual pulled-back module is invertible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 99.10.1: the natural inclusion of the Picard stack into the coherent
stack is representable by open immersions, expressed by its equivalent
open-subscheme criterion for arbitrary base changes. -/
@[stacks 0D03] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.exists_opens_isInvertible_iff :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      [Flat f] → [FinitePresentation f] → [Proper f] →
      ∀ x : CohStack.Obj f, ∃ U : (x.σ.left.left).Opens,
        ∀ {τ : CohStack.SchemesOver B} (h : τ ⟶ x.σ),
          Nonempty (Over.mk h.left.left ⟶ Over.mk U.ι) ↔
            isInvertibleObject ((Modules.pullback (CohStack.fiberMap f h)).obj x.module))
