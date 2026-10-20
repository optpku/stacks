/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Localization.Torsion

/-!
# S-torsion modules as a Serre class

The Serre class of modules in which every element is annihilated by some element of a
multiplicative set `S`, realized as the kernel of localization of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)

#check (ModuleCat.isTorsion' S : ObjectProperty (ModuleCat.{v} R))

#check (ModuleCat.isTorsion'_iff S :
  ∀ M : ModuleCat.{v} R, ModuleCat.isTorsion' S M ↔ Module.IsTorsion' M S)

#check (ModuleCat.isTorsion'_iff_exists_smul_eq_zero S :
  ∀ M : ModuleCat.{v} R,
    ModuleCat.isTorsion' S M ↔ ∀ m : M, ∃ s : S, (s : R) • m = 0)

#check (ModuleCat.instIsSerreClassIsTorsion' S :
  (ModuleCat.isTorsion' S).IsSerreClass)

end ModuleCat
