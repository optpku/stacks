/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Cartesian.FreeAction

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G]
variable (X : Mod C G)

#check (isFree_iff_mono_leftSMul X :
  IsFree X ↔ Mono (ModObj.leftSMul G X.X))

section

variable [IsFree X]

#check (instMonoLeftSMul X : Mono (ModObj.leftSMul G X.X))

end

end CategoryTheory.Mod
