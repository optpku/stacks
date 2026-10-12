/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.5.1: an algebraic space `X` over a scheme `S` is quasi-compact if there exists
a surjective étale morphism `U ⟶ X` with `U` a quasi-compact scheme. -/
@[stacks 03E3] #check (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
