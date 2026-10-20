/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHomProperties
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic

@[expose] public section

/-!
# Base change of ind-smooth ring maps

The owner-level predicate is stable under arbitrary base change. The
tensor-product statement is the normal consumer interface for commutative
algebras.
-/

open scoped TensorProduct

universe u

namespace RingHom.IndSmooth

/-- Ind-smooth ring maps are stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.IndSmooth) := sorry

/-- The tensor-product base change of an ind-smooth algebra map is
ind-smooth. -/
theorem baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (hA : (algebraMap R A).IndSmooth) :
    (algebraMap R' (R' ⊗[R] A)).IndSmooth := sorry

end RingHom.IndSmooth
