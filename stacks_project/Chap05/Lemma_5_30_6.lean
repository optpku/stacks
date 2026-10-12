/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.GrpTopCat.Colimits
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

/- Lemma 5.30.6: colimits and their algebraic forgetful-functor compatibility are reusable
properties of the canonical category `Grp TopCat`. -/
@[stacks 0B21 "topological groups have colimits"]
#check (inferInstance : HasColimits (Grp TopCat.{u}))

@[stacks 0B21 "colimits commute with the forgetful functor to groups"]
#check (inferInstance : PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}))
