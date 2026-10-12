/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) [GrpObj G]

#check (CategoryTheory.Mod.IsPseudoTorsor : Mod C G → Prop)

#check (CategoryTheory.Mod.IsTrivial : Mod C G → Prop)
