/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Away.Nilpotent
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.9.8
@stack 02C5

The standard localization constructions are recalled directly from their
Mathlib owners.  Only the nilpotence characterization needs a thin statement.
-/

universe u

section AtPrime

variable {A : Type u} [CommRing A]

/- Example 10.9.8: the localization of a commutative ring `A` at a prime ideal `p` is the
canonical owner construction `Localization.AtPrime`. -/
@[stacks 02C5 "localization at a prime"]
#check @Localization.AtPrime

end AtPrime

section ModuleAtPrime

variable {A : Type u} [CommRing A]

/- The localization of an `A`-module `M` at the prime ideal `p` is
the canonical owner construction `LocalizedModule.AtPrime`. -/
@[stacks 02C5 "module localization at a prime"]
#check @LocalizedModule.AtPrime

end ModuleAtPrime

section Away

variable {A : Type u} [CommRing A]

/- The localization of `A` with respect to the multiplicative set `{1, f, f^2, ...}` is
the canonical owner construction `Localization.Away`. -/
@[stacks 02C5 "localization away from an element"]
#check @Localization.Away

/- The localization of an `A`-module `M` with respect to `{1, f, f^2, ...}` is
the canonical owner construction `LocalizedModule.Away`. -/
@[stacks 02C5 "module localization away from an element"]
#check @LocalizedModule.Away

@[stacks 02C5 "away localization and nilpotence"]
#check @Localization.Away.subsingleton_iff_isNilpotent

@[stacks 02C5 "nontrivial away localization"]
#check @Localization.Away.nontrivial_iff_not_isNilpotent

end Away

section FractionRing

variable {A : Type u} [CommRing A]

/- The total quotient ring of `A`, i.e. the localization at all non-zero-divisors, is
the canonical owner construction `FractionRing`. -/
@[stacks 02C5 "total quotient ring"]
#check @FractionRing

section

variable [IsDomain A]

/- If `A` is a domain, then its total quotient ring is its field of fractions, expressed by the
canonical `IsFractionRing` instance on `FractionRing A`. -/
@[stacks 02C5 "fraction field of a domain"]
#check (inferInstance : IsFractionRing A (FractionRing A))

end

end FractionRing
