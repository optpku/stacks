/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent.Permanence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Lemma (0HAC) (1): A scheme locally of finite type over a quasi-excellent scheme
is quasi-excellent. -/
@[stacks 0HAC] #check
  (AlgebraicGeometry.Scheme.quasiExcellent_of_locallyOfFiniteType : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.QuasiExcellent S] [LocallyOfFiniteType f], Scheme.QuasiExcellent X)

/- Lemma (0HAC) (2): A scheme locally of finite type over an excellent scheme
is excellent. -/
@[stacks 0HAC] #check
  (AlgebraicGeometry.Scheme.excellent_of_locallyOfFiniteType : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Excellent S] [LocallyOfFiniteType f], Scheme.Excellent X)
