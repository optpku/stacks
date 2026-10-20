module

public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Injective
public import ReasLib.Algebra.Module.Injective.DirectSum

@[expose] public section

open CategoryTheory

universe u v

/-- The polynomial extension of an injective module over a Noetherian commutative ring has
injective dimension at most one. -/
theorem Module.Injective.polynomialExtension_injectiveDimension_le_one
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective A E] :
    CategoryTheory.injectiveDimension
      (ModuleCat.of (Polynomial A) (PolynomialModule A E)) ≤ 1 := sorry

/-- The polynomial extension of an injective module over a Noetherian commutative ring has
finite injective dimension. -/
theorem Module.Injective.polynomialExtension_hasFiniteInjectiveDimension
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective A E] :
    CategoryTheory.injectiveDimension
      (ModuleCat.of (Polynomial A) (PolynomialModule A E)) ≠ ⊤ := sorry
