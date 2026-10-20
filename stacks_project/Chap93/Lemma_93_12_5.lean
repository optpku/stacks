module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion.Smooth
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 93.12.5: Adic completion is smooth for a finite-type algebra smooth
outside the vanishing locus of the completion ideal. -/
@[stacks 0DZ5] #check (FlatAlgebraCat.isSmooth_adicCompletionBasedFunctor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {P : Type u} [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (J : Ideal P),
    (PrimeSpectrum.zeroLocus (J : Set P))ᶜ ⊆ Algebra.smoothLocus k P →
    CategoryTheory.BasedFunctor.IsSmooth
      (FlatAlgebraCat.adicCompletionBasedFunctorOfFiniteType Λ k J))

/- Lemma 93.12.5: The differential of the same completion functor is bijective
on tangent spaces. -/
@[stacks 0DZ5] #check (FlatAlgebraCat.bijective_differential_adicCompletionBasedFunctor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {P : Type u} [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (J : Ideal P),
    (PrimeSpectrum.zeroLocus (J : Set P))ᶜ ⊆ Algebra.smoothLocus k P →
    Function.Bijective (CategoryTheory.BasedFunctor.differential
      (FlatAlgebraCat.adicCompletionBasedFunctorOfFiniteType Λ k J)))
