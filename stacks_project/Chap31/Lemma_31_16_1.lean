/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Affine

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry PrimeSpectrum IsLocalRing

universe u

@[expose] public section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The punctured spectrum of a local ring `A`, viewed as the open complement of the closed point
in `Spec(A)`. -/
def puncturedSpectrumOpen {A : Type u} [CommRing A] [IsLocalRing A] :
    (Spec (CommRingCat.of A)).Opens :=
  ⟨({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint A).isOpen_compl⟩

/- Lemma 31.16.1: for a Noetherian local ring, the punctured spectrum is affine if and only if
the ring has Krull dimension at most one. -/
@[stacks 0BCR] #check
  (AlgebraicGeometry.PuncturedSpectrum.isAffineOpen_iff_ringKrullDim_le_one :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) ↔
        ringKrullDim A ≤ 1)

end
