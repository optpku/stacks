module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange.Faithful
public import ReasLib.Algebra.Module.IdealPower.BaseChange.Bijective
public import ReasLib.RingTheory.RingHom.Quotient.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bijective tensor units on ideal-power torsion modules

This file identifies the quotient-map criterion for the tensor unit to be
bijective on every ideal-power torsion module.

@stack 05E9
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat.IdealPower.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 15.90.2 (05E9): under the flat faithful-base-change setup,
the tensor unit is bijective on every ideal-power torsion module exactly when
the induced quotient map modulo `I` is bijective. -/
@[stacks 05E9]
theorem tensorUnit_bijective_iff_quotientByIdeal_bijective
    (I : Ideal R) (hflat : (algebraMap R S).Flat)
    (hfaithful : (restricted (algebraMap R S) I).Faithful) :
    (∀ M : ModuleCat.{u} R, Module.IsIdealPowerTorsion I M →
      Function.Bijective (TensorProduct.mk R S M 1)) ↔
        Function.Bijective ((algebraMap R S).quotientByIdeal I) := sorry

end ModuleCat.IdealPower.BaseChange
