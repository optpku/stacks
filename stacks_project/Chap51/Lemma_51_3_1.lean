/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Connected
import StacksCheckRecall

@[expose] public section

open scoped ENat

universe u v

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 51.3.1 (1): the punctured spectrum of a Noetherian local ring of depth at
least two is connected. -/
@[stacks 0BLR] #check
  (AlgebraicGeometry.PuncturedSpectrum.connectedSpace_of_moduleDepth_ge_two :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      (2 : ℕ∞) ≤ moduleDepth A A →
        ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme A))

/- Lemma 51.3.1 (2): the punctured spectrum of a henselization of a Noetherian
local ring of depth at least two is connected. -/
@[stacks 0BLR] #check
  (AlgebraicGeometry.PuncturedSpectrum.connectedSpace_henselization_of_moduleDepth_ge_two :
    ∀ (A : Type u) (Ah : Type v)
      [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
      (2 : ℕ∞) ≤ moduleDepth A A →
        ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme Ah))

/- Lemma 51.3.1 (3): the punctured spectrum of a strict henselization of a
Noetherian local ring of depth at least two is connected. -/
@[stacks 0BLR] #check
  (AlgebraicGeometry.PuncturedSpectrum.connectedSpace_strictHenselization_of_moduleDepth_ge_two :
    ∀ (A : Type u) (Ash : Type v)
      [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
      (2 : ℕ∞) ≤ moduleDepth A A →
        ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme Ash))

end AlgebraicGeometry.PuncturedSpectrum
