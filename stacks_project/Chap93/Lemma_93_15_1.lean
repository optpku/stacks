module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.IsolatedSingularities
import StacksCheckRecall

@[expose] public section

open CategoryTheory Algebra PrimeSpectrum RingPairCat RingHom.SquareZeroExtension
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]
variable {ι : Type u} [Finite ι]
variable [henselianPairInclusion.IsRightAdjoint]

/- Lemma 93.15.1: for a finite-type algebra smooth away from finitely many
maximal ideals, localization, henselization, and completion give smooth maps
of deformation categories and isomorphisms on finite-dimensional tangent spaces. -/
@[stacks 0DZF] #check (FlatAlgebraCat.isolatedSingularities_comparison :
  ∀ [Algebra.FiniteType k P] (m : ι → Ideal P) [∀ i, (m i).IsMaximal],
    Function.Injective m →
    (smoothLocus k P)ᶜ ⊆ Set.range (fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) →
    FiniteDimensional k (extOneNaiveCotangent k P P) ∧
      BasedFunctor.IsSmooth (FlatAlgebraCat.localizationPiBasedFunctor Λ k m) ∧
      Function.Bijective (BasedFunctor.differential (FlatAlgebraCat.localizationPiBasedFunctor Λ k m)) ∧
      BasedFunctor.IsSmooth (FlatAlgebraCat.henselizationPiBasedFunctor Λ k m) ∧
      Function.Bijective (BasedFunctor.differential (FlatAlgebraCat.henselizationPiBasedFunctor Λ k m)) ∧
      BasedFunctor.IsSmooth (FlatAlgebraCat.completionPiBasedFunctor Λ k m) ∧
      Function.Bijective (BasedFunctor.differential (FlatAlgebraCat.completionPiBasedFunctor Λ k m)))
