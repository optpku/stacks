module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential

/-!
# Smoothness of henselization of algebra deformations

Pair henselization of a finite-type algebra over a field that is smooth outside
the vanishing locus of the ideal is smooth on deformation categories and induces
a bijection on tangent spaces.
-/

@[expose] public section

open CategoryTheory Functor RingPairCat
open Algebra PrimeSpectrum
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]
variable (J : Ideal P)
variable [henselianPairInclusion.IsRightAdjoint]

/-- Pair henselization of deformations commutes with forgetting to `ArtinianLocalAlgCat`. -/
theorem henselizationFunctor_comp_forget :
    henselizationFunctor Λ k P J ⋙
        deformationForget Λ k (henselizationRing (pairOfIdeal J) : Type u) =
      deformationForget Λ k P :=
  sorry

/-- Pair henselization of algebra deformations as a based functor over the category
of Artinian local algebras. -/
def henselizationBasedFunctor :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor
        (deformationForget Λ k (henselizationRing (pairOfIdeal J) : Type u)) where
  toFunctor := henselizationFunctor Λ k P J
  w := henselizationFunctor_comp_forget Λ k P J

/-- The underlying functor of `henselizationBasedFunctor` is `henselizationFunctor`. -/
theorem henselizationBasedFunctor_toFunctor :
    (henselizationBasedFunctor Λ k P J).toFunctor = henselizationFunctor Λ k P J :=
  sorry

variable {Λ k P}

/-- Pair henselization of deformations of a finite-type algebra is smooth if the
algebra is smooth outside the vanishing locus of the henselization ideal. -/
theorem isSmooth_henselizationBasedFunctor [Algebra.FiniteType k P] (J : Ideal P)
    (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    BasedFunctor.IsSmooth (henselizationBasedFunctor Λ k P J) := sorry

/-- Pair henselization induces a bijection on tangent spaces for a finite-type
algebra smooth outside the vanishing locus of the henselization ideal. -/
theorem bijective_differential_henselizationBasedFunctor [Algebra.FiniteType k P]
    (J : Ideal P) (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    Function.Bijective (BasedFunctor.differential (henselizationBasedFunctor Λ k P J)) :=
  sorry

/-- Pair henselization of deformations is smooth under a registered assertion of
smoothness outside the vanishing locus of the henselization ideal. -/
instance instIsSmooth_henselizationBasedFunctor [Algebra.FiniteType k P]
    (J : Ideal P) [Fact ((zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P)] :
    BasedFunctor.IsSmooth (henselizationBasedFunctor Λ k P J) :=
  isSmooth_henselizationBasedFunctor J Fact.out

end FlatAlgebraCat

end
