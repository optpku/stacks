module

public import stacks_project.Chap52.Lemma_52_12_5_Comparison
public import stacks_project.Chap52.Lemma_52_24_1
public import stacks_project.Chap58.Lemma_58_17_4
public import stacks_project.Chap58.Situation_58_19_1
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AffineAlgebraizationSetup
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.PuncturedSpectrum

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.23.1: in Situation 58.19.1, assume that `A` admits an intrinsic
dualizing complex and is `f`-adically complete. If either `A_f` satisfies `(S₂)`
and every minimal component away from `f` has dimension at least four, or the
primewise depth-plus-dimension bound holds, restriction from finite étale covers
on open neighborhoods in the punctured spectrum of `A` to finite étale covers
of the actual quotient punctured spectrum of `A/(f)` is an equivalence. -/
@[stacks 0DXY] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleNeighborhoodRestriction_isEquivalence_of_dualizing_complete :
  ∀
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A)
    [h_dualizing :
      Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)]
    [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A]
    [h_alternative :
      Fact
        ((SerreConditionS (Localization.Away (f : A)) 2 ∧
          ∀ p : PrimeSpectrum A,
            p.asIdeal ∈ minimalPrimes A →
              (f : A) ∉ p.asIdeal →
                (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
        (∀ p : PrimeSpectrum A,
          p ∉ PrimeSpectrum.zeroLocus ({(f : A)} : Set A) →
            PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus ({(f : A)} : Set A) ≠
              {IsLocalRing.closedPoint A} →
              (3 : EInt) <
                ((WithTop.map Int.ofNat
                  (moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim (A ⧸ p.asIdeal))))]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)),
    Functor.IsEquivalence (principalNeighborhoodRestriction f t))

end AlgebraicGeometry.PuncturedSpectrum
