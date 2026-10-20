/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DerivedEquivalence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 57.18.1: smooth projective schemes over a field are derived equivalent if their
perfect derived categories admit a linear exact equivalence for the structural scalar actions. -/
@[stacks 0G10] #check (@AlgebraicGeometry.SchemeOverField.derivedEquivalent :
  ∀ {k : Type u} [Field k] (X Y : SchemeOverField k),
    [Smooth X.hom] → [Projective X.hom] → [Smooth Y.hom] → [Projective Y.hom] → Prop)

end
