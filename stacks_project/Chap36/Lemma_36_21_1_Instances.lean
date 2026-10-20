/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

#check (AlgebraicGeometry.Scheme.DerivedQCoh.inclusionIsLeftAdjoint :
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
    (inclusion X).IsLeftAdjoint)

end AlgebraicGeometry.Scheme.DerivedQCoh
