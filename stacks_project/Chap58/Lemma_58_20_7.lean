/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.20.7: in Situation 58.19.1, if `V` is finite étale over `U`,
`A` has depth at least `3`, and `V₀` is isomorphic to `Y₀ ×_{X₀} U₀` for some
finite étale `Y₀ → X₀`, then `V` is isomorphic to `Y ×_X U` for some finite
étale `Y → X`. -/
@[stacks 0BLM] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtale_extends_of_depth_ge_three :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ moduleDepth A A)
    (V : Scheme.FiniteEtale (scheme A))
    (Y0 : Scheme.FiniteEtale (Spec (CommRingCat.of (A ⧸ principalIdeal (f : A)))))
    (hV0 : Nonempty
      ((Scheme.finiteEtaleBaseChange (principalQuotientMap f)).obj V ≅
        (Scheme.finiteEtaleBaseChange
          (puncturedOpen (A ⧸ principalIdeal (f : A))).ι).obj Y0))
    , ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
      Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V))

end AlgebraicGeometry.PuncturedSpectrum
