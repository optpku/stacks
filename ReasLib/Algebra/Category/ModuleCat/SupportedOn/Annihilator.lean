module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.RingTheory.Depth.Localization
public import ReasLib.RingTheory.Ideal.Localization

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

/-- For a finite module over a Noetherian ring admitting a dualizing complex, an ideal
supported in `T'` annihilates supported local cohomology through degree `s` exactly when the
corresponding localized depth-plus-dimension inequality holds along every chain `p ⊆ q` with
`p ∉ T'` and `q ∈ T`. -/
theorem exists_annihilator_localCohomology_iff_depth_add_quotientDim
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
    (T T' : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (hTT' : T ⊆ T') (s : ℕ)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ i : ℕ, i ≤ s →
        J ≤ Module.annihilator A
          (ModuleCat.SupportedOn.cohomology T
            (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∀ p q : PrimeSpectrum A,
        p ∉ T' → q ∈ T → p.asIdeal ≤ q.asIdeal →
          (.some (s : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞) +
                ringKrullDim (p.asIdeal.quotientAtPrime q) := sorry

/-- Under a depth-plus-dimension bound along every chain below `p` and every point of
`V(I)` above that chain, an element outside `p` annihilates supported local cohomology
through degree `s`. -/
theorem exists_annihilator_not_mem
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (s : ℕ)
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A))
    (hdepth : ∀ p' q : PrimeSpectrum A,
      p'.asIdeal ≤ p.asIdeal → q ∈ PrimeSpectrum.zeroLocus (I : Set A) →
        p'.asIdeal ≤ q.asIdeal →
          (.some (s : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p'.asIdeal)
              (LocalizedModule.AtPrime p'.asIdeal M)) : WithBot ℕ∞) +
                ringKrullDim (p'.asIdeal.quotientAtPrime q)) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℕ, i ≤ s →
      f ∈ Module.annihilator A
        (ModuleCat.SupportedOn.cohomology (PrimeSpectrum.zeroLocus (I : Set A))
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ)) := sorry

end CategoryTheory.ModuleCat.SupportedOn
