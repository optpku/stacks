/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Resolution.AtPrime

@[expose] public section

universe u v w

variable (R : Type u) (A : Type v) (Λ : Type w)
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]
variable (φ : A →ₐ[R] Λ)

/- Situation 16.9.1: for a finitely presented algebra over a Noetherian base,
`φ.singularIdealIn` is the transported singular ideal.  The chosen target
prime enters the companion resolution predicate, not the ideal itself. -/
#check @AlgHom.singularIdealIn
#check @AlgHom.ResolvableAtPrime
#check @AlgHom.Factorisation.Finite.Resolution
#check @AlgHom.Factorisation.Finite.Resolution.spec
#check @AlgHom.ResolutionAtPrime
#check @AlgHom.ResolutionAtPrime.smoothAt
#check @AlgHom.ResolutionAtPrime.toSmoothAt
#check @AlgHom.ResolutionAtPrime.ofSmoothAt
@[stacks 07F7] #check
  fun (_ : IsNoetherianRing R) (_ : Algebra.FinitePresentation R A)
    (_ : PrimeSpectrum Λ) ↦ (φ.singularIdealIn : Ideal Λ)
