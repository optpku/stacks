/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.Cover
import StacksCheckRecall

universe u

/- Situation 36.9.1: For `X = Spec(A)` and
`U = ⨆ i, PrimeSpectrum.basicOpen (f i)`, this is the canonical open cover of `U`. -/
@[stacks 08CZ] #check
  (AlgebraicGeometry.Spec.BasicOpenUnion.openCover :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A),
      (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) :
        (AlgebraicGeometry.Spec (CommRingCat.of A)).Opens).toScheme.OpenCover)
