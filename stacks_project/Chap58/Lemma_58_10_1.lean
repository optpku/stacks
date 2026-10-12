/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 58.10.1: if a morphism of schemes has dense image, then base change
on finite étale schemes is faithful. -/
@[stacks 0BQE] #check (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_faithful_of_isDominant :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f],
    (AlgebraicGeometry.Scheme.finiteEtaleBaseChange f).Faithful)
