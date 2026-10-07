module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.ZeroDimensional
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
public import ReasLib.RingTheory.KrullDimension.Prime

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- For a normalized dualizing complex over a Noetherian local ring, the localization
at a minimal prime has nontrivial degree-`i` homology exactly when `i` is the
negative of the dimension of the corresponding prime quotient. -/
theorem localizedHomology_nontrivial_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (p : minimalPrimes A) (e : ℕ) (hdim : ringKrullDim (A ⧸ p.1) = e) (i : ℤ) :
    Nontrivial
      (LocalizedModule.AtPrime p.1
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)) ↔
      i = -(e : ℤ) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
