/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) [GrpObj G]

#check (CategoryTheory.Mod.IsPseudoTorsor : Mod C G → Prop)

#check (CategoryTheory.Mod.IsTrivial : Mod C G → Prop)
