/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

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

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The object property of `S`-torsion modules: the kernel of localization at `S`. -/
abbrev isTorsion' (S : Submonoid R) : ObjectProperty (ModuleCat.{v} R) :=
  (localizedModuleFunctor.{v} S).kernel

/-- A bundled module is `S`-torsion iff it is `S`-torsion in the module-theoretic sense. -/
theorem isTorsion'_iff (S : Submonoid R) (M : ModuleCat.{v} R) :
    isTorsion' S M ↔ Module.IsTorsion' M S :=
  sorry

/-- A bundled module is `S`-torsion iff every element is annihilated by some element of `S`. -/
theorem isTorsion'_iff_exists_smul_eq_zero (S : Submonoid R) (M : ModuleCat.{v} R) :
    isTorsion' S M ↔ ∀ m : M, ∃ s : S, (s : R) • m = 0 :=
  sorry

/-- The `S`-torsion modules form a Serre class, as the kernel of exact localization. -/
instance instIsSerreClassIsTorsion' (S : Submonoid R) :
    (isTorsion' S).IsSerreClass :=
  inferInstance

/-- The object property of torsion modules: the kernel of localization at the non-zero-divisors. -/
abbrev isTorsion : ObjectProperty (ModuleCat.{v} R) :=
  isTorsion' (nonZeroDivisors R)

end ModuleCat
