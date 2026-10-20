module

import stacks_project.Chap78.Definition_78_8_1_Action
import ReasLib.CategoryTheory.Monoidal.Cartesian.FreeAction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/- Definition 78.8.2: An action `a : G ×_B X ⟶ X` of a group algebraic space `G` on an
algebraic space `X` over `B` is free when, for every scheme `T` over `B`, the induced
action `G(T) × X(T) → X(T)` is a free action of the group `G(T)` on the set `X(T)`.
The owner is `CategoryTheory.Mod.IsFree` on `GroupAlgebraicSpace.Action G`; a scheme
`T` over `B` is the generalized-point specialization `Z = Over.mk t`. -/
@[stacks 06P8] #check
  (CategoryTheory.Mod.IsFree : AlgebraicGeometry.GroupAlgebraicSpace.Action G → Prop)

variable (X : GroupAlgebraicSpace.Action G)

-- Freeness is cancellation for the action on every type of generalized points of `Over B`.
#check
  (CategoryTheory.Mod.isFree_iff X :
    CategoryTheory.Mod.IsFree X ↔
      ∀ Z : Over B, IsCancelSMul (Z ⟶ G.X) (Z ⟶ X.X))

variable (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B) [CategoryTheory.Mod.IsFree X]

-- Source 'scheme `T` over `B`' is the test object `Over.mk t`.
#check
  (CategoryTheory.Mod.IsFree.instIsCancelSMul X (Over.mk t) :
    IsCancelSMul (Over.mk t ⟶ G.X) (Over.mk t ⟶ X.X))
