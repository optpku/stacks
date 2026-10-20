/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfBase
import StacksCheckRecall

/-!
# Lemma 94.19.1

Constructions A and B induce inverse 2-categorical operations on algebraic stacks.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStacks

/- Lemma 94.19.1: let `Sch_fppf` be a big fppf site and let `g : S ⟶ S'`
be a morphism of this site. Constructions A and B give inverse isomorphisms of
2-categories between algebraic stacks over `S` and pairs `(X', f)` consisting
of an algebraic stack over `S'` and a morphism `f : X' ⟶ overSlice g` over `S'`,
where `overSlice g` is the canonical slice stack `(Sch/S)_fppf`. -/
@[stacks 04X5] #check (AlgebraicGeometry.AlgebraicStacks.toOverSlice.isStrictInverse :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S'),
    StrictPseudofunctor.IsStrictInverse (toOverSlice g) (ofOverSlice g))

end AlgebraicGeometry.AlgebraicStacks
