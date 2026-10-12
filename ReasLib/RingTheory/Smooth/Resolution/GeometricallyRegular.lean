/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.GeometricRegularity
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import ReasLib.RingTheory.Smooth.Resolution.AtPrime
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.Smooth.Resolution.OverField

@[expose] public section

/-!
# Resolution over geometrically regular algebras

The result is stated for an arbitrary algebra homomorphism.  The structural
map associated to a scalar tower is a specialization rather than the owner.
-/

universe u v w

namespace AlgHom.ResolvableAtPrime

/-- Lemma 16.11.4: in positive characteristic, a map from a finitely
presented algebra to a Noetherian geometrically regular algebra is resolvable
at every minimal prime of its transported singular ideal. -/
@[stacks 07FJ]
theorem of_minimal
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ]
    [Algebra k A] [Algebra k Λ] {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra.FinitePresentation k A] [Algebra.IsGeometricallyRegular k Λ]
    [IsNoetherianRing Λ] (φ : A →ₐ[k] Λ)
    (q : PrimeSpectrum Λ)
    (hq : q.asIdeal ∈
      φ.singularIdealIn.minimalPrimes) :
    φ.ResolvableAtPrime q := sorry

end AlgHom.ResolvableAtPrime
