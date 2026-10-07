module

public import ReasLib.Algebra.Module.Injective.Polynomial
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Single

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/-- The degree-zero derived object of the polynomial extension of an injective module over a
Noetherian commutative ring has injective amplitude in `[0, 1]`. -/
theorem Module.Injective.polynomialExtension_hasInjectiveAmplitudeIn
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective A E] :
    DerivedCategory.HasInjectiveAmplitudeIn
      ((DerivedCategory.singleFunctor (ModuleCat (Polynomial A)) (0 : ℤ)).obj
        (ModuleCat.of (Polynomial A) (PolynomialModule A E))) 0 1 := sorry
