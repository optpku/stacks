module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Localization
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential

/-!
# Smoothness of localization of algebra deformations

Localization of a finite-type algebra over a field gives a smooth based functor
with bijective differential when the algebra is smooth on the vanishing locus
of every element of the multiplicative subset.
-/

@[expose] public section

open CategoryTheory
open Algebra
open PrimeSpectrum

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]

namespace FlatAlgebraCat

/-- Localization of deformations of a finite-type algebra over a field is smooth
if the algebra is smooth on the vanishing locus of every element of the
multiplicative subset. -/
theorem isSmooth_localizationBasedFunctor [Algebra.FiniteType k P] (S : Submonoid P)
    (hS : ∀ g ∈ S, zeroLocus ({g} : Set P) ⊆ smoothLocus k P) :
    BasedFunctor.IsSmooth (localizationBasedFunctor Λ k S) := sorry

/-- Localization induces a bijection on tangent spaces of deformations of a
finite-type algebra over a field if the algebra is smooth on the vanishing
locus of every element of the multiplicative subset. -/
theorem bijective_differential_localizationBasedFunctor [Algebra.FiniteType k P]
    (S : Submonoid P)
    (hS : ∀ g ∈ S, zeroLocus ({g} : Set P) ⊆ smoothLocus k P) :
    Function.Bijective (BasedFunctor.differential (localizationBasedFunctor Λ k S)) :=
  sorry

/-- Localization of deformations of a finite-type algebra is smooth under a
registered assertion that the algebra is smooth on the vanishing locus of
every element of the multiplicative subset. -/
instance instIsSmooth_localizationBasedFunctor [Algebra.FiniteType k P]
    (S : Submonoid P)
    [Fact (∀ g ∈ S, PrimeSpectrum.zeroLocus ({g} : Set P) ⊆ Algebra.smoothLocus k P)] :
    BasedFunctor.IsSmooth (localizationBasedFunctor Λ k S) :=
  isSmooth_localizationBasedFunctor S Fact.out

end FlatAlgebraCat
