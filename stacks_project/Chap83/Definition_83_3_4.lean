/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.PreRelation

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
variable (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) (f : X' ⟶ X)

/- Definition 83.3.4 (1): in the situation of Lemma 83.3.3, we call
j' : R' ⟶ U' ×_B U' the base change of the pre-relation j to X'. -/
@[stacks 048H] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.baseChange P hφ f : PreRelation (pullback φ f))

/- Definition 83.3.4 (2): we say it is a flat base change if X' ⟶ X is a
flat morphism of algebraic spaces. -/
@[stacks 048H] #check (AlgebraicGeometry.AlgebraicSpace.Flat f.left : Prop)
