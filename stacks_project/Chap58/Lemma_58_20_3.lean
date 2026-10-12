/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.NormalFiniteEtale
import StacksCheckRecall

/-!
# Finite covers of a normal punctured spectrum

Source erratum for 0BM9: the displayed target must exclude normal components
supported at the closed point. Under the stated hypotheses this is precisely
torsion-freeness over `A`. The unrestricted finite-normal predicate is retained;
the equivalence below uses the explicitly named torsion-free subcategory.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.20.3 (1) -/
@[stacks 0BM9] #check (AlgebraicGeometry.PuncturedSpectrum.globalSections_isEquivalence :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]
      (h_dimension : 2 ≤ ringKrullDim A),
      (AlgebraicGeometry.PuncturedSpectrum.globalSections h_dimension).IsEquivalence)

end AlgebraicGeometry.PuncturedSpectrum

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 58.20.3 (2) -/
@[stacks 0BM9] #check (AlgebraicGeometry.Scheme.Hom.finiteEtale_punctured_extension_iff :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalRing A]
      (h_dimension : 2 ≤ ringKrullDim A)
      (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)),
      let X : Scheme := Spec (CommRingCat.of A)
      let U : X.Opens := PuncturedSpectrum.puncturedOpen A
      let B : CommAlgCat A := Scheme.Hom.globalSectionsAlg (V.hom ≫ U.ι)
      (∃ Y : Scheme.FiniteEtale X,
          Nonempty ((Scheme.finiteEtaleBaseChange U.ι).obj Y ≅ V)) ↔
        CommAlgCat.finiteEtale A B)

end AlgebraicGeometry.Scheme.Hom
