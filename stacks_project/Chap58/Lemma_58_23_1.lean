/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_12_5_Comparison
public import stacks_project.Chap52.Lemma_52_24_1
public import stacks_project.Chap58.Lemma_58_17_4
public import stacks_project.Chap58.Situation_58_19_1

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AffineAlgebraizationSetup
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.PuncturedSpectrum

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable (f : IsLocalRing.maximalIdeal A)

/-- Lemma 58.23.1: in Situation 58.19.1, if `A` has a dualizing complex and is
`f`-adically complete, and either `A_f` is `(S₂)` with every irreducible component
of `X` not contained in `X₀` of dimension at least `4`, or the primewise
depth-dimension inequality holds off `V(f)`, then the restriction functor
`colim_{U₀ ⊂ U' ⊂ U} FÉt_{U'} ⟶ FÉt_{U₀}` identified with
`finiteEtaleNeighborhoodRestriction (idealOnOpen S) t` on the punctured spectrum
`U = PuncturedSpectrum.scheme A` is an equivalence. -/
@[stacks 0DXY]
instance finiteEtaleNeighborhoodRestriction_isEquivalence_of_dualizing_complete
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [h_dualizing :
      Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
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
    (t :
      ColimitCocone
        (finiteEtaleNeighborhoodDiagram
          (idealOnOpen
            (ofPrincipal (IsLocalRing.maximalIdeal A) (f : A) f.property)))) :
    Functor.IsEquivalence
      (finiteEtaleNeighborhoodRestriction
        (idealOnOpen
          (ofPrincipal (IsLocalRing.maximalIdeal A) (f : A) f.property))
        t) := sorry

end AlgebraicGeometry.PuncturedSpectrum
