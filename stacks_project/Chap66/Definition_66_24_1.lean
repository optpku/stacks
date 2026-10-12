/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.24.1: an algebraic space `X` over a scheme `S` is Noetherian if it is
quasi-compact, quasi-separated and locally Noetherian. -/
@[stacks 03EA] #check (AlgebraicGeometry.AlgebraicSpace.IsNoetherian :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
