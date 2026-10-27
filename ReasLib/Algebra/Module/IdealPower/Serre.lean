/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import ReasLib.Algebra.Module.IdealPower.Predicate
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Serre Closure of Ideal-Power Torsion Modules

@stack 05EB
@stack 0A6K

For a finitely generated ideal, ideal-power torsion is closed under extensions and defines
a Serre class of modules. Finite generation is a sufficient hypothesis; it need not be
necessary for a particular ideal.
-/

noncomputable section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- After quotienting by the `I`-primary component, no nonzero element is annihilated by `I`
when `I` is finitely generated. -/
@[stacks 05EB "torsion-free quotient by the primary component"]
theorem powerTorsion_quotient_primaryComponent_eq_bot
    (I : Ideal R) (hI : I.FG) :
    I.powerTorsion (M ⧸ I.primaryComponent M) 1 = ⊥ := sorry
-- Proof strategy: lift a torsion class to `M`, use finite generation of `I` to combine the
-- quotient witnesses into one power, and conclude that the lift lies in `I.primaryComponent M`.

end Ideal

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- For a finitely generated ideal `I`, an extension of two `I`-power torsion modules
is `I`-power torsion. -/
@[stacks 05EB "extension closure"]
theorem isIdealPowerTorsion_of_submodule_quotient
    (I : Ideal R) (hI : I.FG) (N : Submodule R M)
    (hN : IsIdealPowerTorsion I N)
    (hQ : IsIdealPowerTorsion I (M ⧸ N)) :
    IsIdealPowerTorsion I M := sorry
-- Proof strategy: for each `x : M`, annihilate its quotient class by one power of `I`,
-- choose finite generators `a_j` of that power of `I`, then choose a common exponent
-- `m` killing all `a_j * x` in `N`; consequently `I ^ (m + n) * x = 0`.

end Module

namespace CategoryTheory.ModuleCat

variable {R : Type u} [CommRing R]

/-- The object property of modules that are power torsion for `I`. -/
@[stacks 0A6K "ideal-power torsion object property"]
abbrev isIdealPowerTorsion (I : Ideal R) : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.IsIdealPowerTorsion I M

/-- For a finitely generated ideal `I`, the `I`-power torsion modules form a Serre class. -/
@[stacks 0A6K]
instance isIdealPowerTorsion_isSerreClass (I : Ideal R) [Fact I.FG] :
    (isIdealPowerTorsion I : ObjectProperty (ModuleCat.{v} R)).IsSerreClass := sorry
-- Proof strategy: supply the subobject and quotient closure from the elementwise criterion,
-- and use `Module.isIdealPowerTorsion_of_submodule_quotient` for extension closure.

end CategoryTheory.ModuleCat
