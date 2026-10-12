/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.BaseChange
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 39.13.6 (1): base change along `f : S' ⟶ S` sends a groupoid scheme over `S`
to a groupoid scheme over `S'`. -/
@[stacks 0DT8] #check (AlgebraicGeometry.GroupoidScheme.baseChange :
  {S S' : AlgebraicGeometry.Scheme.{u}} → (S' ⟶ S) →
    AlgebraicGeometry.GroupoidScheme S → AlgebraicGeometry.GroupoidScheme S')

/- Lemma 39.13.6 (2): after transporting the base-changed groupoid scheme back over `S`
via `Over.map f`, the canonical object and arrow projections form a morphism of groupoid
schemes. -/
@[stacks 0DT8] #check (AlgebraicGeometry.GroupoidScheme.baseChangeProjection :
  {S S' : AlgebraicGeometry.Scheme.{u}} → (f : S' ⟶ S) →
    (G : AlgebraicGeometry.GroupoidScheme S) →
      AlgebraicGeometry.GroupoidScheme.Hom
        (AlgebraicGeometry.GroupoidScheme.changeBase f
          (AlgebraicGeometry.GroupoidScheme.baseChange f G)) G)
