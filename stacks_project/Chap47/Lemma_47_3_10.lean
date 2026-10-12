/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Polynomial
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/- Lemma 47.3.10: If `A` is Noetherian and `E` is an injective `A`-module, then the
polynomial extension `PolynomialModule A E`, canonically representing
`E ⊗[A] Polynomial A`, has injective amplitude `[0, 1]` over `Polynomial A` when placed
in degree zero.
-/
@[stacks 0A6J] #check
  (Module.Injective.polynomialExtension_hasInjectiveAmplitudeIn :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective A E],
      DerivedCategory.HasInjectiveAmplitudeIn
        ((DerivedCategory.singleFunctor (ModuleCat (Polynomial A)) (0 : ℤ)).obj
          (ModuleCat.of (Polynomial A) (PolynomialModule A E))) 0 1)

-- The same polynomial extension has finite injective dimension as a module.
#check
  (Module.Injective.polynomialExtension_hasFiniteInjectiveDimension :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      (E : Type v) [AddCommGroup E] [Module A E] [Module.Injective A E],
      CategoryTheory.injectiveDimension
        (ModuleCat.of (Polynomial A) (PolynomialModule A E)) ≠ ⊤)
