module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Depth
import StacksCheckRecall

universe u

open CategoryTheory

/- Definition 51.13.1: for an ideal `I` of a Noetherian ring `A` and
`K ∈ D⁺[ModuleCat.isFinitePresentation A]`, the `I`-depth of `K` is the largest
element of `WithTop ℤ` below which all supported local cohomology objects vanish.
For a local ring, `DerivedCategory.depth` specializes this to the maximal ideal. -/
@[stacks 0EHY] #check (Ideal.derivedDepth :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion I)
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)), WithTop ℤ)

#check (CategoryTheory.DerivedCategory.depth :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (RΓ : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion
      (IsLocalRing.maximalIdeal A) ⊣ RΓ)
    (K : DerivedCategory.Plus.CohomologyIn
      (ModuleCat.isFinitePresentation A)), WithTop ℤ)
