/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Punctured spectra

The punctured spectrum is explicit open-subscheme data, not an existential
package. Its point constructor makes nonemptiness arguments reusable.
-/

@[expose] public section

open AlgebraicGeometry PrimeSpectrum IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The punctured spectrum of a local ring, the open complement of its closed point. -/
@[stacks 01IY "punctured spectrum"]
def puncturedOpen : (Spec (CommRingCat.of A)).Opens :=
  ⟨({closedPoint A} : Set (PrimeSpectrum A))ᶜ,
    (isClosed_singleton_closedPoint A).isOpen_compl⟩

/-- A prime belongs to the punctured spectrum exactly when it is not the closed point. -/
@[simp]
theorem mem_puncturedOpen_iff_ne_closedPoint (p : PrimeSpectrum A) :
    p ∈ puncturedOpen A ↔ p ≠ closedPoint A := sorry

/-- A prime belongs to the punctured spectrum exactly when it is not the maximal ideal. -/
theorem mem_puncturedOpen_iff_ne_maximalIdeal (p : PrimeSpectrum A) :
    p ∈ puncturedOpen A ↔ p.asIdeal ≠ maximalIdeal A := sorry

/-- The punctured spectrum as an open subscheme. -/
@[stacks 01IY "punctured spectrum scheme"]
abbrev scheme : Scheme.{u} := (puncturedOpen A).toScheme

/-- A nonclosed prime gives an explicit point of the punctured spectrum. -/
@[stacks 01IY "punctured-spectrum point"]
def point (p : PrimeSpectrum A) (hp : p ≠ closedPoint A) : scheme A :=
  ⟨p, (mem_puncturedOpen_iff_ne_closedPoint A p).2 hp⟩

/-- The ambient prime underlying a punctured-spectrum point is the chosen prime. -/
@[simp, stacks 01IY "punctured-spectrum point value"]
theorem point_val (p : PrimeSpectrum A) (hp : p ≠ closedPoint A) :
    (point A p hp).1 = p := sorry

end AlgebraicGeometry.PuncturedSpectrum
