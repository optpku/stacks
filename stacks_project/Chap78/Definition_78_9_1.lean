/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap78.Definition_78_8_1_Action
import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/- Definition 78.9.1 (1): The `G`-action on `X` is a pseudo `G`-torsor, or formally
principally homogeneous under `G`, when `ModObj.leftSMul` is an isomorphism over `B`. -/
@[stacks 04TW] #check
  (CategoryTheory.Mod.IsPseudoTorsor : GroupAlgebraicSpace.Action G → Prop)

/- Definition 78.9.1 (2): A pseudo `G`-torsor is trivial when it is `G`-equivariantly
isomorphic over `B` to `G` with its regular left action. -/
@[stacks 04TW] #check
  (CategoryTheory.Mod.IsTrivial : GroupAlgebraicSpace.Action G → Prop)
