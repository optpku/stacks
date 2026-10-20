module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization.Smooth
import StacksCheckRecall

/-!
# Smoothness of henselization of ring deformation categories

For a finite-type algebra smooth outside the vanishing locus of an ideal, pair
henselization is smooth on deformation categories and identifies tangent spaces.
-/

public section

open CategoryTheory Algebra PrimeSpectrum RingPairCat

universe u

/- Lemma 93.14.3 (1): for a finite-type `k`-algebra `P` smooth on the complement
of `V(J)`, the canonical deformation functor `Def_P ⟶ Def_{P^h}` is smooth. -/
@[stacks 0DZD] #check (FlatAlgebraCat.isSmooth_henselizationBasedFunctor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {P : Type u} [CommRing P] [Algebra k P]
    [henselianPairInclusion.IsRightAdjoint] [Algebra.FiniteType k P] (J : Ideal P)
    (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P),
    BasedFunctor.IsSmooth (FlatAlgebraCat.henselizationBasedFunctor Λ k P J))

/- Lemma 93.14.3 (2): for a finite-type `k`-algebra `P` smooth on the complement
of `V(J)`, pair henselization induces a bijection on tangent spaces. -/
@[stacks 0DZD] #check (FlatAlgebraCat.bijective_differential_henselizationBasedFunctor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {P : Type u} [CommRing P] [Algebra k P]
    [henselianPairInclusion.IsRightAdjoint] [Algebra.FiniteType k P] (J : Ideal P)
    (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P),
    Function.Bijective
      (BasedFunctor.differential (FlatAlgebraCat.henselizationBasedFunctor Λ k P J)))

end
