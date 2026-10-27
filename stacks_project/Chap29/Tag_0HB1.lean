/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Lemma (0HB1). The structure map of X over S is f ≫ g, where g is the
structure map of Y. If X is étale over S and Y is unramified over S, then f is étale. -/
@[stacks 0HB1] #check (AlgebraicGeometry.Etale.of_comp_of_unramified :
  ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Etale (f ≫ g)] [Unramified g], Etale f)
