/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.NormalLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Remark 52.20.2 (1): completeness and Noetherianity supply a dualizing complex,
as required by assumption (2) of Lemma 52.20.1. -/
@[stacks 0DXV] #check (CategoryTheory.DerivedCategory.IsDualizing.exists_of_completeLocal :
  (A : Type u) → [CommRing A] → [IsNoetherianRing A] → [IsCompleteLocalRing A] →
    ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)

/- Remark 52.20.2 (2): the depth-dimension inequality on the punctured vanishing
locus supplies assumption (5) of Lemma 52.20.1. -/
@[stacks 0DXV] #check (IsNormalRing.one_lt_depth_quotient_add_dim :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
    [IsCompleteLocalRing A] → [IsNormalRing A] →
    4 ≤ ringKrullDim A → (f : A) → f ∈ IsLocalRing.maximalIdeal A → f ≠ 0 →
    ∀ p : PrimeSpectrum A,
      p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
        p ≠ IsLocalRing.closedPoint A →
          (.some (1 : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal
                (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
              WithBot ℕ∞) +
              ringKrullDim (A ⧸ p.asIdeal))

/- Remark 52.20.2 (3): the depth-dimension inequality outside the vanishing locus
supplies assumption (6) of Lemma 52.20.1. -/
@[stacks 0DXV] #check (IsNormalRing.three_lt_depth_add_dim :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
    [IsCompleteLocalRing A] → [IsNormalRing A] →
    4 ≤ ringKrullDim A → (f : A) → f ∈ IsLocalRing.maximalIdeal A → f ≠ 0 →
    ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
        PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) ≠
          {IsLocalRing.closedPoint A} →
          (.some (3 : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal A)) : WithBot ℕ∞) +
              ringKrullDim (A ⧸ p.asIdeal))

/- Remark 52.20.2 (4): finite locally free coherent formal modules on the principal
completion of the punctured spectrum admit coherent algebraizations. Locality and
the principal-ideal setup in assumptions (1) and (3) of Lemma 52.20.1 are supplied
by the existing binders; regularity follows from normal-local domain inference
and IsRegular.of_ne_zero. Compare Lemma 52.20.4 and Remark 52.20.7. -/
@[stacks 0DXV] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_normal_local_dim_ge_four :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      [IsCompleteLocalRing A] → [IsNormalRing A] → [Fact (4 ≤ ringKrullDim A)] →
      (S : AffineAlgebraizationSetup A) →
      (F : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) →
      (f : A) → S.a = IsLocalRing.maximalIdeal A → S.I = Ideal.span ({f} : Set A) →
      f ∈ IsLocalRing.maximalIdeal A → f ≠ 0 →
      (∀ n : ℕ, IsFiniteLocallyFreeStage F n) →
      (CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
