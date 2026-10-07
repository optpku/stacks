module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 58.20.2 -/
@[stacks 0BLK] #check (AlgebraicGeometry.Scheme.Hom.finiteEtale_punctured_iff_globalSections :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)),
      (2 : ℕ∞) ≤ moduleDepth A A →
      let X : Scheme := Spec (CommRingCat.of A)
      let U : X.Opens := PuncturedSpectrum.puncturedOpen A
      let B : CommAlgCat A := Scheme.Hom.globalSectionsAlg (V.hom ≫ U.ι)
      (∃ Y : Scheme.FiniteEtale X,
          Nonempty ((Scheme.finiteEtaleBaseChange U.ι).obj Y ≅ V)) ↔
        CommAlgCat.finiteEtale A B)

end AlgebraicGeometry.Scheme.Hom
