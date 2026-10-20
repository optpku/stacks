/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Localization.Torsion
public import ReasLib.Algebra.Category.ModuleCat.Localization.SerreQuotient
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/- Proposition 110.77.2: for a commutative ring `R`, the Serre quotient of `ModuleCat R` by the
Serre class of torsion modules is canonically equivalent to `ModuleCat (FractionRing R)`, via the
induced functor of localization at the non-zero-divisors. -/
@[stacks 0B0K] #check (ModuleCat.inducedLocalizedFunctor_isEquivalence (nonZeroDivisors R) :
  (ModuleCat.inducedLocalizedFunctor (nonZeroDivisors R) :
    ModuleCat.isTorsion.isoModSerre.Localization ⥤
      ModuleCat.{v} (FractionRing R)).IsEquivalence)

end ModuleCat
