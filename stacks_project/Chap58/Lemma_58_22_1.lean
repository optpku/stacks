module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Faithful
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.22.1 (1): if `U' ⊂ U` is open containing `U0` and every minimal
prime of `A` in `U' \ U0` has dimension at least two, then restriction of
finite étale covers `FÉt_{U'} ⟶ FÉt_{U0}` along the open-immersion lift of
the principal-quotient map `U0 ⟶ U` is faithful. -/
@[stacks 0BLN] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_faithful_of_minimalPrimeDimOn :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : maximalIdeal A) (U' : (scheme A).Opens)
      (h0 : Set.range (principalQuotientMap f) ⊆ Set.range U'.ι)
      [Fact (minimalPrimeDimGeTwoOn f U')],
      (Scheme.finiteEtaleBaseChange
        (IsOpenImmersion.lift U'.ι (principalQuotientMap f) h0)).Faithful)

/- Lemma 58.22.1 (2): there exists an open `U' ⊂ U` containing the image of
the principal-quotient map `U0 ⟶ U` that satisfies the dimension hypothesis
of (1). -/
@[stacks 0BLN] #check
  (AlgebraicGeometry.PuncturedSpectrum.exists_open_minimalPrimeDimGeTwoOn :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : maximalIdeal A),
      ∃ U' : (scheme A).Opens,
        Set.range (principalQuotientMap f) ⊆ Set.range U'.ι ∧
          minimalPrimeDimGeTwoOn f U')

/- Lemma 58.22.1 (3): the dimension hypothesis of (1) is inherited by any
smaller open `U'' ⊂ U'` that still contains the image of `U0`. -/
@[stacks 0BLN] #check
  (AlgebraicGeometry.PuncturedSpectrum.minimalPrimeDimGeTwoOn_mono :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] (f : maximalIdeal A)
      {U' U'' : (scheme A).Opens} (hUU : U'' ≤ U')
      (h0 : Set.range (principalQuotientMap f) ⊆ Set.range U''.ι)
      (hdim : minimalPrimeDimGeTwoOn f U'),
      minimalPrimeDimGeTwoOn f U'')

/- Lemma 58.22.1 (4): the colimit restriction
`colim_{U0 ⊂ U' ⊂ U} FÉt_{U'} ⟶ FÉt_{U0}` is faithful, where `U0` is the
actual punctured spectrum of `A ⧸ principalIdeal (f : A)`. -/
@[stacks 0BLN] #check
  (AlgebraicGeometry.PuncturedSpectrum.principalNeighborhoodRestriction_faithful :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : maximalIdeal A)
      (t : ColimitCocone
        (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)),
      (principalNeighborhoodRestriction f t).Faithful)

end AlgebraicGeometry.PuncturedSpectrum
