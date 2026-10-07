module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.LocalConditions
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Set TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.20.6 (local erratum): in Situation 52.16.1, a coherent formal module satisfies the
`(2, 3)`-inequalities when the ring is local with maximal ideal `S.a`, has a
dualizing complex and cohomological dimension one for `S.I`, its completed
stalks are finite locally free away from the completed ideal, and either
every localization outside `V(I)` satisfies `(S₂)` with the required component dimension
bound or the stated primewise depth-plus-dimension bound holds. The unbound source element
`f` is corrected to the complement of `V(I)` throughout, following the source proof;
no principality of `I` is assumed and the uploaded source is unchanged. -/
@[stacks 0EJB] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.satisfiesInequalities_of_local_conditions :
  ∀
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (hcd : Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_finiteLocallyFree :
      ∀ y : S.Y, (hy : S.y y ∈ S.U) →
        ∀ g : completedLocalRing S (closedFiberOpenPoint S y hy),
          g ∈ completedIdeal S (closedFiberOpenPoint S y hy) →
            Module.FiniteLocallyFree (Localization.Away g)
              (LocalizedModule.Away g
                (completedStalk S F (closedFiberOpenPoint S y hy))))
    (h_alternative :
      ((∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (S.I : Set A) →
          SerreConditionS (Localization.AtPrime p.asIdeal) 2) ∧
        (∀ Z : irreducibleComponents S.X,
          ¬ ((Z : Set S.X) ⊆ Set.range S.y) →
            (4 : WithBot ℕ∞) ≤ topologicalKrullDim Z)) ∨
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (S.I : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (S.I : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (3 : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (A ⧸ p.asIdeal)))),
    SatisfiesInequalities S F 2 3)

end AlgebraicGeometry.Scheme.CoherentFormalModules
