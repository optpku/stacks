module

import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteCompletion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 58.20.4: for a Noetherian local ring, a finite etale cover of the
punctured spectrum extends over the spectrum if and only if its canonical
pullback to the punctured spectrum of the adic completion extends over the
completed spectrum. -/
@[stacks 0BLL] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtale_punctured_completion_iff :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)),
    let X : Scheme := Spec (CommRingCat.of A)
    let U : X.Opens := PuncturedSpectrum.puncturedOpen A
    let Ahat : Type u := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let X' : Scheme := Spec (CommRingCat.of Ahat)
    let U' : X'.Opens := PuncturedSpectrum.puncturedOpen Ahat
    let V' : Scheme.FiniteEtale (PuncturedSpectrum.scheme Ahat) :=
      (Scheme.finiteEtaleBaseChange (PuncturedSpectrum.completionMap A)).obj V
    (∃ Y : Scheme.FiniteEtale X,
        Nonempty ((Scheme.finiteEtaleBaseChange U.ι).obj Y ≅ V)) ↔
      (∃ Y' : Scheme.FiniteEtale X',
        Nonempty ((Scheme.finiteEtaleBaseChange U'.ι).obj Y' ≅ V')))

end AlgebraicGeometry.Scheme.Hom
