/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generalization-stable closed subsets and finite flat modules

@stack 052U
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- Lemma 10.108.6 (Stacks 052U): closed subsets of `Spec R` stable under
generalization are open exactly when finite flat modules are finite locally free. -/
@[stacks 052U]
theorem closed_stableUnderGeneralization_isOpen_iff_finiteFlat_finiteLocallyFree :
    (∀ Z : Set (PrimeSpectrum R), IsClosed Z → StableUnderGeneralization Z → IsOpen Z) ↔
      ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M],
        Module.FiniteLocallyFree R M := sorry

end PrimeSpectrum
