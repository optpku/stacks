/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Enough injectives from injective resolutions

Degree zero of an injective resolution gives an injective presentation of its object.
-/

@[expose] public section

universe v u

namespace CategoryTheory

/-- An abelian category in which every object admits an injective resolution has enough
injectives. -/
noncomputable instance enoughInjectivesOfHasInjectiveResolutions
    (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C] :
    EnoughInjectives C where
  presentation X := ⟨{
    J := (injectiveResolution X).cocomplex.X 0
    f := (injectiveResolution X).ι.f 0
    mono := Limits.mono_of_isLimit_fork (injectiveResolution X).isLimitKernelFork }⟩

end CategoryTheory
