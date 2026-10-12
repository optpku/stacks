/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

/- Definition 101.23.2: a morphism `f : X ⟶ Y` of algebraic stacks is
locally quasi-finite if it is quasi-DM, locally of finite type, and for
every morphism `Spec(k) ⟶ Y` where `k` is a field the space `|X_k|` is
discrete. -/
@[stacks 06PU] #check AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
