/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange
public import ReasLib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithful base change on ideal-power torsion modules

The four equivalent flatness and faithfulness conditions are stated using the
canonical quotient map and the restricted extension-of-scalars functor.

@stack 05E7
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat.IdealPower.BaseChange

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 15.90.1 (05E7): flatness together with faithful flatness of
the quotient, surjectivity on quotient spectra, faithfulness on quotient
modules, and faithfulness on ideal-power torsion modules are equivalent. -/
@[stacks 05E7]
theorem faithful_tfae (f : R →+* S) (I : Ideal R) :
    List.TFAE
      [ f.Flat ∧ (f.quotientByIdeal I).FaithfullyFlat
      , f.Flat ∧ Function.Surjective
          (PrimeSpectrum.comap (f.quotientByIdeal I))
      , f.Flat ∧ (ModuleCat.extendScalars (f.quotientByIdeal I)).Faithful
      , f.Flat ∧ (restricted f I).Faithful
      ] := sorry

end ModuleCat.IdealPower.BaseChange
