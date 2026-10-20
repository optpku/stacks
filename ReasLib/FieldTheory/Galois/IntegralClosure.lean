module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Invariant.Profinite
public import ReasLib.FieldTheory.Galois.KrullTopology

@[expose] public section

/-!
# Galois actions on integral closures

This file owns the reusable bridge from a possibly infinite Galois extension
of fraction fields to the induced profinite action on an integral closure.  It
uses Mathlib's canonical integral-closure action and does not install a second
action through `IsIntegralClosure.MulSemiringAction`.

@stack 0BRK
@stack 09EA
-/

open scoped Pointwise

universe u v w

namespace integralClosure

variable {A : Type u} {L : Type w}
variable [CommRing A] [Field L] [Algebra A L]

/-- If `K` is a fraction field of `A` and `L / K` is Galois, then `L` is a
fraction field of the integral closure of `A` in `L`. -/
@[stacks 0BRK "fraction field of an integral closure in a Galois extension"]
theorem isFractionRing_of_isGalois
    (K : Type v) [Field K] [Algebra A K] [IsDomain A] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [IsGalois K L] :
    IsFractionRing (integralClosure A L) L := sorry
-- Proof strategy: derive `Algebra.IsAlgebraic A L` from the algebraic Galois extension `L / K`
-- through `IsFractionRing.comap_isAlgebraic_iff`, then apply
-- `IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L)`; injectivity of
-- `algebraMap A L` follows from the two field embeddings and `IsScalarTower.algebraMap_eq`.

/-- The Galois group of `L / K` is the canonical Galois group of the integral
closure of `A` in `L` over an integrally closed domain `A`. -/
@[stacks 0BRK "Galois group of an integral closure"]
instance isGaloisGroup
    {K : Type v} [Field K] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] [IsGalois K L] :
    IsGaloisGroup Gal(L/K) A (integralClosure A L) := sorry
-- Proof strategy: install `isFractionRing_of_isGalois K`, use the canonical
-- `FieldExtension.IsGaloisGroup.of_isGalois` action on `L / K`, and apply
-- `IsGaloisGroup.of_isFractionRing` to descend the field action to the integral closure; its
-- integrality over `A` is the canonical `integralClosure` instance.

/-- With the discrete topology, the canonical Galois action on an integral
closure is continuous. -/
@[stacks 0BRK "continuous Galois action on a discrete integral closure"]
instance continuousSMul
    {K : Type v} [Field K] [Algebra A K] [Algebra K L]
    [IsScalarTower A K L] [IsGalois K L]
    [TopologicalSpace (integralClosure A L)]
    [DiscreteTopology (integralClosure A L)] :
    ContinuousSMul Gal(L/K) (integralClosure A L) := sorry
-- Proof strategy: use `continuousSMul_iff_stabilizer_isOpen`. For an element of the integral
-- closure, identify its stabilizer with the stabilizer of its coercion to `L`, then apply
-- `FieldExtension.stabilizer_isOpen_of_isIntegral` to its defining integrality proof.

/-- The Galois group acts transitively on prime ideals of an integral closure
having the same contraction to the base domain. -/
@[stacks 0BRK "Galois transitivity on primes of an integral closure",
  stacks 09EA "Lemma 15.113.1 transitivity on maximal ideals"]
theorem exists_smul_eq_of_under_eq
    {K : Type v} [Field K] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (q q' : Ideal (integralClosure A L)) [q.IsPrime] [q'.IsPrime]
    (hunder : q.under A = q'.under A) :
    ∃ σ : Gal(L/K), σ • q = q' := sorry
-- Proof strategy: use the `Algebra.IsInvariant` instance supplied by `isGaloisGroup` together
-- with the discrete continuous action above, then apply
-- `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` to `q` and `q'`; reverse the
-- returned equality `q' = σ • q` to match this orientation.

end integralClosure
