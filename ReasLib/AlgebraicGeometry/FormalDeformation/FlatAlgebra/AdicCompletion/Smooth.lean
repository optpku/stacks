/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential

/-!
# Smoothness of adic completion of algebra deformations

For a finite-type algebra over a field that is smooth outside the vanishing locus
of an ideal, adic completion gives a smooth based functor with bijective differential.
-/

@[expose] public section

open CategoryTheory Functor
open Algebra PrimeSpectrum
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]

namespace FlatAlgebraCat

variable (Λ k) in
/-- Adic completion of deformations of a finite-type residue-field algebra as a
based functor over the category of Artinian local algebras. -/
noncomputable def adicCompletionBasedFunctorOfFiniteType [Algebra.FiniteType k P]
    (J : Ideal P) :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (AdicCompletion J P)) :=
  -- Local instance justification (noncanonical choice): the field k supplies Noetherianity of P through Algebra.FiniteType.isNoetherianRing k P, but k cannot be inferred from the instance target IsNoetherianRing P.
  letI := Algebra.FiniteType.isNoetherianRing k P
  adicCompletionBasedFunctor Λ k P J

/-- Completing a finite-type deformation preserves its Artinian local base. -/
theorem adicCompletionBasedFunctorOfFiniteType_obj_base [Algebra.FiniteType k P]
    (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionBasedFunctorOfFiniteType Λ k J).toFunctor.obj ξ).left.base =
      ξ.left.base := rfl

/-- Adic completion of deformations of a finite-type algebra is smooth if the
algebra is smooth outside the vanishing locus of the completion ideal. -/
theorem isSmooth_adicCompletionBasedFunctor [Algebra.FiniteType k P] (J : Ideal P)
    (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    BasedFunctor.IsSmooth (adicCompletionBasedFunctorOfFiniteType Λ k J) := sorry

/-- Adic completion induces a bijection on tangent spaces for a finite-type
algebra smooth outside the vanishing locus of the completion ideal. -/
theorem bijective_differential_adicCompletionBasedFunctor [Algebra.FiniteType k P]
    (J : Ideal P) (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    Function.Bijective
      (BasedFunctor.differential (adicCompletionBasedFunctorOfFiniteType Λ k J)) :=
  sorry

/-- Adic completion of deformations is smooth under a registered assertion of
smoothness outside the vanishing locus of the completion ideal. -/
instance instIsSmooth_adicCompletionBasedFunctorOfFiniteType [Algebra.FiniteType k P]
    (J : Ideal P) [Fact ((zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P)] :
    BasedFunctor.IsSmooth (adicCompletionBasedFunctorOfFiniteType Λ k J) :=
  isSmooth_adicCompletionBasedFunctor J Fact.out

end FlatAlgebraCat
