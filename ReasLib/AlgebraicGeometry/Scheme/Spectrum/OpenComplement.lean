/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Open complements of ideal zero loci

The complement of the zero locus of an ideal is an open subset of its affine spectrum.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable {A : Type u} [CommRing A]

/-- The open complement `Spec A ∖ V(I)` of the zero locus of an ideal. -/
def idealComplementOpens (I : Ideal A) : (Spec (.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A prime belongs to the open complement of an ideal exactly when it is outside its zero
locus. -/
theorem mem_idealComplementOpens_iff (I : Ideal A) (p : PrimeSpectrum A) :
    p ∈ idealComplementOpens I ↔ p ∉ PrimeSpectrum.zeroLocus (I : Set A) := sorry

end AlgebraicGeometry.Scheme
