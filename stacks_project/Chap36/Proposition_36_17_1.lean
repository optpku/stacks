/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Compact
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Proposition 36.17.1: an object of `D_QCoh(𝒪_X)` on a quasi-compact and
quasi-separated scheme is compact if and only if its underlying derived
`𝒪_X`-module is perfect. -/
@[stacks 09M1] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.isCompactObject_iff_isPerfect :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (E : AlgebraicGeometry.Scheme.DerivedQCoh X),
      IsCompactObject E ↔ AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E.obj)
