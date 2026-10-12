/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteCompletion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 58.19.3: finite morphisms over the punctured spectrum descend from the
maximal-ideal completion, with compatible identifications after restriction and completion. -/
@[stacks 0BLH] #check
  (AlgebraicGeometry.Scheme.Hom.exists_finite_morphism_of_completion :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {V Y' : Scheme.{u}}
    (v : V ⟶ PuncturedSpectrum.scheme A) [IsFinite v]
    (y' : Y' ⟶
      Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
      [IsFinite y']
    (h : Nonempty
      (Over.mk (pullback.snd v (PuncturedSpectrum.completionMap A)) ≅
        Over.mk
          (pullback.snd y'
            (PuncturedSpectrum.puncturedOpen
              (AdicCompletion (IsLocalRing.maximalIdeal A) A)).ι))),
    ∃ (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of A)),
      IsFinite y ∧
        Nonempty
          (Over.mk v ≅
            Over.mk (pullback.snd y (PuncturedSpectrum.puncturedOpen A).ι)) ∧
        Nonempty
          (Over.mk y' ≅
            Over.mk (pullback.snd y (PuncturedSpectrum.completionSpecMap A))))
