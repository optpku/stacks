/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.24.1: a finite-type morphism to an irreducible scheme whose generic fiber is empty
has empty base change over some nonempty open subscheme of the target. -/
@[stacks 054W] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_of_isEmpty_genericFiber :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f] [IrreducibleSpace Y],
      IsEmpty (f.fiber (genericPoint Y)) →
        ∃ V : Y.Opens, Nonempty V ∧ IsEmpty (Limits.pullback V.ι f : Scheme))
