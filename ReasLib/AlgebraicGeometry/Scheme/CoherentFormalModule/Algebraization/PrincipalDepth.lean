module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.PrincipalFiniteLocalCohomology
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Depth.Localization
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A principal regular ideal with finite locally free stages and the stated
depth-dimension bounds admits a canonical extension of the formal module. -/
theorem canonicallyExtends_of_principal_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (f : A)
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_I : S.I = Ideal.span ({f} : Set A))
    (h_f_mem : f ∈ IsLocalRing.maximalIdeal A)
    (h_f_regular : IsRegular f)
    (h_stageFree : ∀ n : ℕ,
      IsFiniteLocallyFreeStage F n)
    (h_depth_on_V :
      ∀ p : PrimeSpectrum A,
        p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          p ≠ IsLocalRing.closedPoint A →
            (.some (1 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal
                  (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
                WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal))
    (h_depth_off_V :
      ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (.some (3 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal)) :
    CanonicallyExtends S F := sorry

/-- If the ring is complete local, the canonical extension from the principal
depth-dimension criterion lies in the coherent-completion essential image. -/
theorem isCompletion_of_principal_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsCompleteLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (f : A)
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_I : S.I = Ideal.span ({f} : Set A))
    (h_f_mem : f ∈ IsLocalRing.maximalIdeal A)
    (h_f_regular : IsRegular f)
    (h_stageFree : ∀ n : ℕ,
      IsFiniteLocallyFreeStage F n)
    (h_depth_on_V :
      ∀ p : PrimeSpectrum A,
        p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          p ≠ IsLocalRing.closedPoint A →
            (.some (1 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal
                  (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
                WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal))
    (h_depth_off_V :
      ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (.some (3 : ℕ∞) : WithBot ℕ∞) <
              (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal A)) : WithBot ℕ∞) +
                ringKrullDim (A ⧸ p.asIdeal)) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
