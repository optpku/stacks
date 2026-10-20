module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.LocalComparison
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Product.Tangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential
public import ReasLib.RingTheory.Extension.Cotangent.FiniteDimensional

/-!
# Deformation comparisons at isolated singularities

For a finite-type algebra smooth away from finitely many distinct closed points,
localization, henselization, and completion give smooth deformation comparisons
and bijections of tangent spaces.
-/

@[expose] public section

open CategoryTheory Algebra PrimeSpectrum RingPairCat RingHom.SquareZeroExtension
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]
variable {ι : Type u} [Finite ι]

namespace FlatAlgebraCat

/-- Localization at distinct maximal ideals containing the nonsmooth locus of a
finite-type algebra induces a smooth map to the equibased product of local deformations. -/
theorem isSmooth_localizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    BasedFunctor.IsSmooth (localizationPiBasedFunctor Λ k m) :=
  sorry

/-- The canonical localization comparison is smooth when injectivity and
containment of the nonsmooth locus are registered. -/
instance instIsSmooth_localizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] [Fact (Function.Injective m)]
    [Fact ((smoothLocus k P)ᶜ ⊆
      Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P))] :
    BasedFunctor.IsSmooth (localizationPiBasedFunctor Λ k m) :=
  isSmooth_localizationPiBasedFunctor m Fact.out Fact.out

/-- Localization at distinct maximal ideals containing the nonsmooth locus of a
finite-type algebra induces a bijection on tangent spaces. -/
theorem bijective_differential_localizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    Function.Bijective (BasedFunctor.differential (localizationPiBasedFunctor Λ k m)) :=
  sorry

variable [henselianPairInclusion.IsRightAdjoint]

/-- For a finite-type algebra smooth outside finitely many distinct closed points,
factorwise henselization of the corresponding local deformations is smooth. -/
theorem isSmooth_henselizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k m) :=
  sorry

/-- The canonical henselization comparison is smooth when injectivity and
containment of the nonsmooth locus are registered. -/
instance instIsSmooth_henselizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] [Fact (Function.Injective m)]
    [Fact ((smoothLocus k P)ᶜ ⊆
      Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P))] :
    BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k m) :=
  isSmooth_henselizationPiBasedFunctor m Fact.out Fact.out

/-- For a finite-type algebra smooth outside finitely many distinct closed points,
factorwise henselization of the corresponding local deformations induces a bijection
on tangent spaces. -/
theorem bijective_differential_henselizationPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    Function.Bijective (BasedFunctor.differential (henselizationPiBasedFunctor Λ k m)) :=
  sorry

/-- For a finite-type algebra smooth outside finitely many distinct closed points,
factorwise completion of henselian local deformations is smooth. -/
theorem isSmooth_completionPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k m) :=
  sorry

/-- The canonical completion comparison is smooth when injectivity and
containment of the nonsmooth locus are registered. -/
instance instIsSmooth_completionPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] [Fact (Function.Injective m)]
    [Fact ((smoothLocus k P)ᶜ ⊆
      Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P))] :
    BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k m) :=
  isSmooth_completionPiBasedFunctor m Fact.out Fact.out

/-- For a finite-type algebra smooth outside finitely many distinct closed points,
factorwise completion of henselian local deformations induces a bijection on tangent spaces. -/
theorem bijective_differential_completionPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    Function.Bijective (BasedFunctor.differential (completionPiBasedFunctor Λ k m)) :=
  sorry

/-- For a finite-type algebra smooth away from finitely many distinct maximal
ideals, the first cotangent extension space is finite-dimensional and the canonical
localization, henselization, and completion comparisons are smooth and induce
bijections on tangent spaces. -/
theorem isolatedSingularities_comparison [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (hm : Function.Injective m)
    (hsmooth : (smoothLocus k P)ᶜ ⊆ Set.range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)) :
    FiniteDimensional k (extOneNaiveCotangent k P P) ∧
      BasedFunctor.IsSmooth (localizationPiBasedFunctor Λ k m) ∧
      Function.Bijective (BasedFunctor.differential (localizationPiBasedFunctor Λ k m)) ∧
      BasedFunctor.IsSmooth (henselizationPiBasedFunctor Λ k m) ∧
      Function.Bijective (BasedFunctor.differential (henselizationPiBasedFunctor Λ k m)) ∧
      BasedFunctor.IsSmooth (completionPiBasedFunctor Λ k m) ∧
      Function.Bijective (BasedFunctor.differential (completionPiBasedFunctor Λ k m)) := by
  refine ⟨finiteDimensional_extOneNaiveCotangent_of_finite_nonsmooth k P
    ((Set.finite_range fun i ↦ (⟨m i, inferInstance⟩ : PrimeSpectrum P)).subset hsmooth), ?_⟩
  exact ⟨isSmooth_localizationPiBasedFunctor m hm hsmooth,
    bijective_differential_localizationPiBasedFunctor m hm hsmooth,
    isSmooth_henselizationPiBasedFunctor m hm hsmooth,
    bijective_differential_henselizationPiBasedFunctor m hm hsmooth,
    isSmooth_completionPiBasedFunctor m hm hsmooth,
    bijective_differential_completionPiBasedFunctor m hm hsmooth⟩

end FlatAlgebraCat
