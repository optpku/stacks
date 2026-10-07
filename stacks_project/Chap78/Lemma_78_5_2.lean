module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.BaseChange
public import stacks_project.Chap78.Lemma_78_5_2_Over

/-!
# Base change of group algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 78.5.2: Let `B` be an algebraic space over a scheme `S`. Let `G` be a
group algebraic space over `B`. Let `f : B' ⟶ B` be a morphism of algebraic
spaces over `S`. The pullback `(G_{B'}, m_{B'})` is a group algebraic space
over `B'`. -/
@[stacks 043I] #check (AlgebraicGeometry.GroupAlgebraicSpace.baseChange :
  ∀ {S : Scheme.{u}} {B B' : AlgebraicSpace S},
    GroupAlgebraicSpace B → (B' ⟶ B) → GroupAlgebraicSpace B')

/-- Slice base change of a group algebraic space along a morphism of bases. -/
abbrev grpOverPullback {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (f : B' ⟶ B) : GroupAlgebraicSpace B' :=
  GroupAlgebraicSpace.baseChange G f

end AlgebraicGeometry.AlgebraicSpace
