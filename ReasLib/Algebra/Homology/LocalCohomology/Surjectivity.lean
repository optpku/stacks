module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.LocalRing.Defs
public import ReasLib.RingTheory.Ideal.MinimalPrime.TopDimension

@[expose] public section

universe u

namespace localCohomology

/-- If `f` avoids every top-dimensional minimal prime of a Noetherian local ring
`A` of dimension `d`, then multiplication by `f` is surjective on degree-`d`
local cohomology for every finite `A`-module and every ideal of support. -/
theorem smul_surjective_of_notMem_topDim {A M : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (d : ℕ) (hdim : ringKrullDim A = d) (f : A)
    (h_notMem : ∀ p ∈ minimalPrimes.topDim A, f ∉ p) (I : Ideal A) :
    Function.Surjective
      (LinearMap.lsmul A ((localCohomology I d).obj (ModuleCat.of A M)) f) := sorry

end localCohomology
