module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleDualizing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.20.5: in Situation 58.19.1, if `A` has a dualizing complex, the
pair `(A, (f))` is henselian, and either `A_f` is `(S₂)` with every irreducible
component of `X` not contained in `X₀` of dimension at least `3`, or
`depth(A_p) + dim(A ⧸ p) > 2` for every prime `p` not containing `f`, then a
finite étale `V` over `U` whose pullback to `U₀` is isomorphic to the pullback
of some finite étale `Y₀` over `X₀` already extends to a finite étale `Y` over
`X`. -/
@[stacks 0EK6] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtale_extends_of_henselian_dualizing :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (f : maximalIdeal A)
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [HenselianRing A (principalIdeal f)]
    [Fact
      ((SerreConditionS (Localization.Away (f : A)) 2 ∧
        ∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            (f : A) ∉ p.asIdeal →
              (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
      (∀ p : PrimeSpectrum A,
        (f : A) ∉ p.asIdeal →
          (2 : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (A ⧸ p.asIdeal))))]
    (V : Scheme.FiniteEtale (scheme A))
    (Y0 : Scheme.FiniteEtale (Spec (CommRingCat.of (A ⧸ principalIdeal (f : A)))))
    (hV0 : Nonempty
      ((Scheme.finiteEtaleBaseChange (principalQuotientMap f)).obj V ≅
        (Scheme.finiteEtaleBaseChange (puncturedOpen (A ⧸ principalIdeal (f : A))).ι).obj Y0)),
    ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
      Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V))

end AlgebraicGeometry.PuncturedSpectrum
