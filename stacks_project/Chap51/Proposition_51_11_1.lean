module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.FinitenessCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u

/- Proposition 51.11.1: for a Noetherian ring with a dualizing complex, a
specialization-stable subset `T` of its spectrum, and a finite module `M`,
supported cohomology is finite through degree `s` exactly when the
depth-plus-quotient-dimension inequality holds along every prime chain from
outside `T` into `T`. -/
@[stacks 0EFD]
#check
  (@CategoryTheory.ModuleCat.SupportedOn.cohomology_finite_iff_depth_add_quotientDim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) (s : ℕ)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
    (∀ i : ℕ, i ≤ s →
      Module.Finite A
        (ModuleCat.SupportedOn.cohomology T
          (ModuleCat.single0 (ModuleCat.of A M)) (i : ℤ))) ↔
      ∀ p q : PrimeSpectrum A,
        p ∉ T → q ∈ T → p.asIdeal ≤ q.asIdeal →
          (.some (s : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞) +
                ringKrullDim (p.asIdeal.quotientAtPrime q))
