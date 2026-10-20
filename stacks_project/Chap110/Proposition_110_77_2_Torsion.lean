/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Localization.Torsion

/-!
# Torsion modules as a Serre class

The classical Serre class of torsion modules, obtained by specializing `S`-torsion to the
multiplicative set of non-zero-divisors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

#check (ModuleCat.isTorsion : ObjectProperty (ModuleCat.{v} R))

#check (ModuleCat.isTorsion'_iff (nonZeroDivisors R) :
  ∀ M : ModuleCat.{v} R, ModuleCat.isTorsion M ↔ Module.IsTorsion R M)

#check (ModuleCat.isTorsion'_iff_exists_smul_eq_zero (nonZeroDivisors R) :
  ∀ M : ModuleCat.{v} R,
    ModuleCat.isTorsion M ↔ ∀ m : M, ∃ a : nonZeroDivisors R, (a : R) • m = 0)

#check (ModuleCat.instIsSerreClassIsTorsion' (nonZeroDivisors R) :
  (ModuleCat.isTorsion : ObjectProperty (ModuleCat.{v} R)).IsSerreClass)

end ModuleCat
