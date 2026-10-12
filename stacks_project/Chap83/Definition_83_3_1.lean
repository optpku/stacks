/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : PreRelation U) (φ : U ⟶ X)

/- Definition 83.3.1 (1): a morphism `φ : U ⟶ X` of algebraic spaces over `B` is
`R`-invariant for a pre-relation `j = (t, s) : R ⟶ U ×_B U` when the square with
legs `t`, `s`, `φ`, `φ` commutes, i.e. `t ≫ φ = s ≫ φ`. -/
@[stacks 048E] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsInvariantHom :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B},
      PreRelation U → (U ⟶ X) → Prop)

variable (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G)
variable {Y : Over B} (ψ : Xg.X ⟶ Y)

/- Definition 83.3.1 (2): if the pre-relation comes from the action of a group
algebraic space `G` on `U` over `B` as in Lemma 78.15.1, the same condition is
called `G`-invariance. -/
@[stacks 048E] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsInvariantHom
    (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation
      (AlgebraicGeometry.GroupoidAlgebraicSpace.ofAction G Xg)) ψ : Prop)
